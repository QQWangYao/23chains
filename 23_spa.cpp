/* 
 * Copyright: Cristobal Leiva and Nicolas Theriault
 * To compile (example for 512 bits): g++ 23_spa.cpp -o 23 -Wall -std=c++11 -O3 -D BITS=512
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

/* Convert big integers from string hexadecimal representation into a bitset */
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
    uint8_t carry = 0, carry_aux;
    uint64_t msb;
    dest->msb = 0;
    dest->num.reset();
    for(int64_t i = orig->msb; i >= 0; i--)
    {
        msb = dest->msb-1;
        if(orig->num.test(i))
        {
            carry_aux = carry+1;
            if(carry == 1)
            {
                if(carry_aux == 3)
                {
                    carry = 0;
                    dest->num.set(i, true);
                    dest->msb = (i > dest->msb) ? msb+1: msb+1;
                }
                else
                {
                    carry = 0;
                    dest->num.set(i, true);
                    dest->msb = (i > dest->msb) ? i+1: msb+1;
                }
            }
            else 
            {
                if(carry_aux == 3)
                {
                    carry = 2;
                    dest->num.set(i, true);
                    dest->msb = (i > dest->msb) ? i+1: msb+1;
                }
                else
                {
                    carry = 1;
                    dest->num.set(i, false);
                    dest->msb = (i > dest->msb) ? msb+1: msb+1;
                }
            }
            orig->zero = false;
        }
        else
        {
            carry_aux = carry+1;
            if(carry == 1)
            {
                if(carry_aux == 3)
                {
                    carry = 2;
                    dest->num.set(i, false);
                    dest->msb = (i > dest->msb) ? i+1: msb+1;
                }
                else
                {
                    carry = 2;
                    dest->num.set(i, false);
                    dest->msb = (i > dest->msb) ? msb+1: msb+1;
                }
            }
            else
            {
                if(carry_aux == 3)
                {
                    carry = 1;
                    dest->num.set(i, true);
                    dest->msb = (i > dest->msb) ? i+1: msb+1;
                }
                else
                {
                    carry = 0;
                    dest->num.set(i, false);
                    dest->msb = (i > dest->msb) ? msb+1: msb+1;
                }
            }
        }
    }
    dest->zero = (dest->msb > 0) ? false: true;
}

static inline void step(int64_t v1, int64_t *v2, int64_t j, int64_t i, int64_t mov)
{
    int64_t tmp1, tmp2, clear;
    tmp1 = v1;
    tmp2 = *v2;
    /* Wipe left or right side of bits before setting new values. 
     * To clear left side and keep right side unchanged: &= 15 (xxxx-1111).
     * To clear right side and keep left side unchanged: &= 240 (1111-xxxx). */
    clear = (mov < 16) ? 240: 15;
    if(tmp1 < tmp2)
    {
        *v2 = tmp1;
        T[j][i] &= clear;
        T[j][i] |= mov;
    }
    else
    {
        *v2 = tmp2;
        T[j][i] &= 255;
        T[j][i] |= 0;
    }
}

static inline void shorter_chain(int64_t i, int64_t j, int8_t row, chainptr_t shortest)
{
    int64_t weight = P_weight[row][i];
    int64_t shortest_weight = shortest->weight, shortest_i = shortest->i, shortest_j = shortest->j;
    if(weight < shortest_weight)
    {
        shortest->weight = weight;
        shortest->i = i;
        shortest->j = j;
    }
    else
    {
        shortest->weight = shortest_weight;
        shortest->i = shortest_i;
        shortest->j = shortest_j;
    }
}

void optimal_chain(bigint_t a, chainptr_t shortest)
{
    bigint_t b ;
    int64_t i, j, size;
    int8_t curr, next, aux;
    /* Initialization */
    for(i = 0; i < max_size; i++)
        P_weight[0][i] = N_weight[0][i] = max_size;
    /* base case */
    shortest->weight = max_size;
    P_weight[0][0] = j = curr = 0;
    next = 1;
    while(!a.zero)
    {
        divide_by_3(&a, &b);
        size = a.msb;
        P_weight[next][size+1] = N_weight[next][size+1] = max_size;
        P_weight[next][size+2] = N_weight[next][size+2] = max_size;
        for(i = 0; i <= size; i++)
        {
            P_weight[next][i] = N_weight[next][i] = max_size;
            /* Horizontal steps */
            if(a.num.test(i))
            {
                step(N_weight[curr][i], &N_weight[curr][i+1], j, i+1, 64); /* (H, -, 0) => 0100-xxxx */
                step(P_weight[curr][i]+1, &P_weight[curr][i+1], j, i+1, 1); /* H, +, +1) => xxxx-0001 */
                step(P_weight[curr][i]+1, &N_weight[curr][i+1], j, i+1, 48); /* (H, +, -1) => 0011-xxxx */
            }
            else
            {
                step(P_weight[curr][i], &P_weight[curr][i+1], j, i+1, 0); /* (H, +, 0) => xxxx-0000 */
                step(N_weight[curr][i]+1, &N_weight[curr][i+1], j, i+1, 112); /* (H, -, -1) => 0111-xxxx */
                step(N_weight[curr][i]+1, &P_weight[curr][i+1], j, i+1, 5); /* (H, -, +1) => xxxx-0101 */
            }
            /* Vertical steps */
            if(!a.zero)
            {
                if(a.num.test(i) ^ b.num.test(i))
                {
                    if(a.num.test(i) ^ a.num.test(i+1) ^ b.num.test(i+1))
                    {
                        P_weight[next][i] = P_weight[curr][i]+1;
                        N_weight[next][i] = max_size;
                        T[j+1][i] = 9; /* (V, +, +1) => xxxx-1001 */
                        step(N_weight[curr][i]+1, &N_weight[next][i], j+1, i, 240); /* (V, -, -1) => 1111-xxxx */
                    }
                    else
                    {
                        P_weight[next][i] = P_weight[curr][i]+1;
                        N_weight[next][i] = max_size;
                        T[j+1][i] = 9; /* (V, +, +1) => xxxx-1001 */
                        step(N_weight[curr][i]+1, &N_weight[next][i], j+1, i, 240); /* (V, -, -1) = 1111-xxxx */
                    }
                }
                else
                {
                    if(a.num.test(i) ^ a.num.test(i+1) ^ b.num.test(i+1))
                    {                        
                        N_weight[next][i] = N_weight[curr][i];
                        P_weight[next][i] = max_size;
                        T[j+1][i] = 192; /* (V, -, 0) => 1100-xxxx */
                        step(P_weight[curr][i]+1, &N_weight[next][i], j+1, i, 176);  /* (V, +, -1) => 1011-xxxx */
                    }
                    else
                    {
                        P_weight[next][i] = P_weight[curr][i];
                        N_weight[next][i] = max_size;
                        T[j+1][i] = 8; /* (V, +, 0) => 1000-xxxx */
                        step(N_weight[curr][i]+1, &P_weight[next][i], j+1, i, 13); /* (V, -, +1) => xxxx-1101 */
                    }
                }
            }
        }
        /* Check if this iteration produced a chain shorter than the shortest so far */
        shorter_chain(size+1, j, curr, shortest);
        shorter_chain(size+2, j, curr, shortest);
        size = b.msb;
        shorter_chain(size+1, j, next, shortest);
        shorter_chain(size+2, j, next, shortest);
        /* Next iteration */
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

