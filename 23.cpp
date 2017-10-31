/* 
 * Copyright: Cristobal Leiva and Nicolas Theriault
 * To compile (example for 512 bits): g++ 23.cpp -o 23 -Wall -std=c++11 -O3 -D BITS=512
 * To run: ./23 scalar_in_hexadecimal 
 * Example for 512 bits: ./23 b518b0217e7f9c3701b8d6bc3d8757c8b961d1b2acb3355ca833c9d5d538b0e0113d44f37feedf5a3cd5617fc979cd1375f60e4c7006b079b67a73b2ea660ab5
 */
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <bitset>
#include <chrono>
#include <iostream>
#ifndef BITS
    #define BITS 256
#endif

static const int64_t max_size = BITS+4;

/*
 * Weights of positive (P_weight) and negative (N_weight) chains.
 * We just need two rows of information for previous and current chains.
 * */
int64_t P_weight[2][max_size], N_weight[2][max_size];

/*
 * 'Movements array' for storing information for every chain.
 * Every term needs 4 bits of information:
 *      - 1 bit to know whether we did a doubling (0) or tripling (1) to get here (horizontal or vertical step).
 *      - 1 bit to know whether the previous chain was positive (0) or negative (1).
 *      - 2 bits to know if we got here by doing nothing (00), adding a term (01) or substracting a term (11).
 *
 * For example, if we got to some chain by making a vertical step (tripling) from a negative chain and we added
 * a negative term, that means $n_{i,j} = \overline{\mathscr{C}}_{i,j-1} - 2^{i}3^{j-1}$. In this code, this will
 * be denoted as (V, -, -1).
 *
 * int8_t provides 8 bits, so we use the first half of bits for storing information of positive chains
 * and last 4 bits for storing information of negative chains.
 *
 * Example: We zero first half of bits and then store a movement of the type (H, +, -1) which translates to
 * setting bits 0011:
 *
 * T[j][i+1] &= ~(15 << 0);
 * T[j][i+1] |= (3 << 0);
 *
 * Example: We zero second half of bits and then store a movement of the type (V, -, -1) which translates to
 * settings bits 1111:
 *
 * T[j+1][i] &= ~(15 << 4);
 * T[j+1][i] |= (15 << 4);
 *
 * */
int8_t T[max_size][max_size];

typedef struct {
    int64_t weight;
    int64_t i;
    int64_t j;
} chain_t;

typedef chain_t* chainptr_t;

typedef struct {
    std::bitset<max_size> num;
    int64_t msb;
    bool zero;
} bigint_t;

typedef bigint_t* bigintptr_t;

/* Convert big integers from string decimal representation into a bitset */
void str_to_bits(char *orig, bigintptr_t dest)
{
    uint8_t digit;
    uint64_t bitcount = 0;
    std::bitset<max_size> mask;
    for(int64_t i = strlen(orig)-1; i >= 0; i--)
    {
        digit = (orig[i] > '9') ? (orig[i] &~ 0x20)-'A'+10: (orig[i]-'0');
        mask = std::bitset<max_size>(digit);
        dest->num |= (mask << bitcount);
        bitcount += 4;
    }
    dest->zero = (bitcount > 0) ? false: true;
    dest->msb = bitcount;
}

/* Manually divide by 3 by looking at bits and keeping track of carries */
void divide_by_3(bigintptr_t orig, bigintptr_t dest)
{
    uint8_t carry = 0;
    orig->zero = true;
    dest->zero = true;
    dest->msb = 0;
    dest->num.reset();
    for(int64_t i = orig->msb; i >= 0; i--)
    {
        if(orig->num.test(i))
        {
            if(carry == 1)
            {
                dest->num.set(i);
                carry--;
                dest->zero = false;
                if(i > dest->msb) dest->msb = i+1;
            }
            else if(carry == 2)
            {
                dest->num.set(i);
                dest->zero = false;
                if(i > dest->msb) dest->msb = i+1;
            }
            else
                carry++;
            orig->zero = false;
        }
        else
        {
            if(carry == 1)
                carry++;
            else if(carry == 2)
            {
                dest->num.set(i);
                carry--;
                dest->zero = false;
                if(i > dest->msb) dest->msb = i+1;
            }
        }
    }
}

void optimal_chain(bigint_t a, chainptr_t shortest)
{
    bigint_t b ;
    int64_t i, j, size, cont;
    int8_t curr, next, aux;
    /* Initialization */
    for(i = 0; i < max_size; i++)
        P_weight[0][i] = N_weight[0][i] = max_size;
    shortest->weight = max_size;
    P_weight[0][0] = 0; /* base case */
    j = 0;
    curr = 0;
    next = 1;
    while(!a.zero)
    {
        divide_by_3(&a, &b);
        cont = 0;
        size = a.msb;
        P_weight[next][size+1] = N_weight[next][size+1] = max_size;
        P_weight[next][size+2] = N_weight[next][size+2] = max_size;
        for(i = 0; i <= size; i++)
        {
            /* We don't need to check all the cases if weights of both positive and negative chains
             * are equal or greater than the shortest chain found so far */
            if(P_weight[curr][i] >= shortest->weight && N_weight[curr][i] >= shortest->weight)
            {
                P_weight[next][i] = N_weight[next][i] = max_size;
                cont++;
            }
            else
            {
                /* Horizontal steps */
                if(a.num.test(i))
                {
                    if(N_weight[curr][i] < N_weight[curr][i+1]) /* (H, -, 0) */
                    {
                        N_weight[curr][i+1] = N_weight[curr][i];
                        T[j][i+1] &= 15;
                        T[j][i+1] |= 64; /* 0100 */
                    }
                    if(P_weight[curr][i]+1 < P_weight[curr][i+1]) /* (H, +, +1) */
                    {
                        P_weight[curr][i+1] = P_weight[curr][i]+1;
                        T[j][i+1] &= 240;
                        T[j][i+1] |= 1; /* 0001 */
                    }
                    if(P_weight[curr][i]+1 < N_weight[curr][i+1]) /* (H, +, -1) */
                    {
                        N_weight[curr][i+1] = P_weight[curr][i]+1;
                        T[j][i+1] &= 15;
                        T[j][i+1] |= 48; /* 0011 */
                    }
                }
                else /* bit == 0 */
                {
                    if(P_weight[curr][i] < P_weight[curr][i+1]) /* (H, +, 0) */
                    {
                        P_weight[curr][i+1] = P_weight[curr][i];
                        T[j][i+1] &= 240;
                    }
                    if(N_weight[curr][i]+1 < N_weight[curr][i+1]) /* (H, -, -1) */
                    {
                        N_weight[curr][i+1] = N_weight[curr][i]+1;
                        T[j][i+1] &= 15;
                        T[j][i+1] |= 112; /* 0111 */
                    }
                    if(N_weight[curr][i]+1 < P_weight[curr][i+1]) /* (H, -, +1) */
                    {
                        P_weight[curr][i+1] = N_weight[curr][i]+1;
                        T[j][i+1] &= 240;
                        T[j][i+1] |= 5; /* 0101 */
                    }
                }
                /* Vertical steps */
                if(!a.zero)
                {
                    if(a.num.test(i) ^ b.num.test(i))
                    {
                        P_weight[next][i] = P_weight[curr][i]+1;
                        N_weight[next][i] = N_weight[curr][i]+1;
                        T[j+1][i] = 249; /* 1111 and 1001 */
                    }
                    else
                    {
                        if(a.num.test(i) ^ a.num.test(i+1) ^ b.num.test(i+1))
                        {
                            P_weight[next][i] = max_size;
                            N_weight[next][i] = P_weight[curr][i]+1;
                            T[j+1][i] = 176; /* 1011 and 0000 */
                            if(N_weight[curr][i] < N_weight[next][i]) /* (V, -, 0) */
                            {
                                N_weight[next][i] = N_weight[curr][i];
                                T[j+1][i] &= 15;
                                T[j+1][i] |= 192; /* 1100 */
                            }
                        }
                        else
                        {
                            N_weight[next][i] = max_size;
                            P_weight[next][i] = P_weight[curr][i];
                            T[j+1][i] = 8; /* 0000 and 1000 */
                            if(N_weight[curr][i]+1 < P_weight[next][i]) /* (V, -, +1) */
                            {
                                P_weight[next][i] = N_weight[curr][i]+1;
                                T[j+1][i] &= 240;
                                T[j+1][i] |= 13; /* 1101 */
                            }
                        }
                    }
                }
            }
        }
        /* Check if this iteration produced a chain shorter than the shortest so far */
        if(P_weight[curr][size+1] < shortest->weight)
        {
            shortest->weight = P_weight[curr][size+1];
            shortest->i = size+1;
            shortest->j = j;
        }
        if(P_weight[curr][size+2] < shortest->weight)
        {
            shortest->weight = P_weight[curr][size+2];
            shortest->i = size+2;
            shortest->j = j;
        }
        if(a.zero) break;
        size = b.msb;
        if(P_weight[next][size+1] < shortest->weight)
        {
            shortest->weight = P_weight[next][size+1];
            shortest->i = size+1;
            shortest->j = j+1;
        }
        if(P_weight[next][size+2] < shortest->weight)
        {
            shortest->weight = P_weight[next][size+2];
            shortest->i = size+2;
            shortest->j = j+1;
        }
        if(cont >= a.msb) break;
        a = b;
        j++;
        aux = curr;
        curr = next;
        next = aux;
    }
}

/* Backtrack from the information of the shortest chain and the information array T */
void print_chain(chainptr_t chain)
{
    int64_t i = chain->i;
    int64_t j = chain->j;
    int8_t base = 0;
    bool type = T[j][i] & 8;
    bool sign = T[j][i] & 4;
    bool change_sign = T[j][i] & 2;
    bool change_value = T[j][i] & 1;
    while(chain->weight > 0)
    {
        (type) ? (j--): (i--);
        if(change_value)
        {
            (change_sign) ? (printf(" - ")): (printf(" + "));
            printf("2^(%" PRIu64 ")*3^(%" PRIu64 ")", i, j);
            chain->weight--;
        }
        (sign) ? (base = 4): (base = 0);
        type = T[j][i] & (1 << (base+3));
        sign = T[j][i] & (1 << (base+2));
        change_sign = T[j][i] & (1 << (base+1));
        change_value = T[j][i] & (1 << base);
    }
    printf("\n");
}

int main(int argc, char *argv[])
{
    if(argc != 2)
    {
        printf("\nUsage: %s hexadecimal_integer\n\n", argv[0]);
        exit(1);
    }
    
    bigint_t n;
    str_to_bits(argv[1], &n);
    chain_t shortest;
    
    auto start = std::chrono::steady_clock::now();
    optimal_chain(n, &shortest);
    auto end = std::chrono::steady_clock::now();
    
    std::cout << "# Time: ";
    std::cout << (std::chrono::duration_cast<std::chrono::microseconds>(end-start).count()) << std::endl;
    std::cout << " microseg" << std::endl;
    
    printf("# Minimum of %" PRIu64 "\n", shortest.weight);
    print_chain(&shortest);
    
    return 0;
}

