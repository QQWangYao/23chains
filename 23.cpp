/* Copyright: Cristobal Leiva and Nicolas Theriault */
/* To compile (example for 256 bits): g++ 23.cpp -o 23 -Wall -std=c++11 -O3 -D BITS=256 */
/* To run: ./23 scalar */
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
    bool zero;
    uint8_t digit, carry;
    dest->zero = true;
    dest->msb = 0;
    do
    {
        zero = true;
        carry = 0;
        for(uint64_t i = 0; i < strlen(orig); i++)
        {
            digit = carry*10 + orig[i]-'0';
            if(digit != 0)
            {
                (digit%2 == 0) ? (carry = 0): (carry = 1);
                orig[i] = (digit >> 1)+'0';
                if(zero) zero = false;
                if(dest->zero) dest->zero = false;
            }
        }
        if(carry == 1) dest->num.set(dest->msb);
        dest->msb++;
    }
    while(!zero);
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
    bigint_t b;
    int64_t i, j, size, cont;
    int8_t curr, next, aux;
    /* Initialization */
    for(i = 0; i < max_size; i++)
        P_weight[0][i] = N_weight[0][i] = INT_MAX;
    shortest->weight = INT_MAX;
    P_weight[0][0] = 0; /* base case */
    j = 0;
    curr = 0;
    next = 1;
    while(!a.zero)
    {
        divide_by_3(&a, &b);
        cont = 0;
        size = a.msb;
        P_weight[next][size+1] = N_weight[next][size+1] = INT_MAX;
        P_weight[next][size+2] = N_weight[next][size+2] = INT_MAX;
        for(i = 0; i <= size; i++)
        {
            P_weight[next][i] = N_weight[next][i] = INT_MAX;
            /* No need of checking all the cases if the weights of positive and negative chains
             * are equal or greater than the shortest chain so far */
            if(P_weight[curr][i] >= shortest->weight && N_weight[curr][i] >= shortest->weight)
                cont++;
            else
            {
                /* Horizontal steps */
                if(a.num.test(i))
                {
                    if(P_weight[curr][i]+1 < P_weight[curr][i+1]) /* (H, +, +1) */
                    {
                        P_weight[curr][i+1] = P_weight[curr][i]+1;
                        T[j][i+1] &= ~(15 << 0);
                        T[j][i+1] |= (1 << 0); /* 0001 */
                    }
                    if(P_weight[curr][i]+1 < N_weight[curr][i+1]) /* (H, +, -1) */
                    {
                        N_weight[curr][i+1] = P_weight[curr][i]+1;
                        T[j][i+1] &= ~(15 << 4);
                        T[j][i+1] |= (3 << 4); /* 0011 */
                    }
                    if(N_weight[curr][i] < N_weight[curr][i+1]) /* (H, -, 0) */
                    {
                        N_weight[curr][i+1] = N_weight[curr][i];
                        T[j][i+1] &= ~(15 << 4);
                        T[j][i+1] |= (4 << 4); /* 0100 */
                    }
                }
                else /* bit == 0 */
                {
                    if(P_weight[curr][i] < P_weight[curr][i+1]) /* (H, +, 0) */
                    {
                        P_weight[curr][i+1] = P_weight[curr][i];
                        T[j][i+1] &= ~(15 << 0);
                    }
                    if(N_weight[curr][i]+1 < P_weight[curr][i+1]) /* (H, -, +1) */
                    {
                        P_weight[curr][i+1] = N_weight[curr][i]+1;
                        T[j][i+1] &= ~(15 << 0);
                        T[j][i+1] |= (5 << 0); /* 0101 */
                    }
                    if(N_weight[curr][i]+1 < N_weight[curr][i+1]) /* (H, -, -1) */
                    {
                        N_weight[curr][i+1] = N_weight[curr][i]+1;
                        T[j][i+1] &= ~(15 << 4);
                        T[j][i+1] |= (7 << 4); /* 0111 */
                    }
                }
                /* Vertical steps */
                if(!a.zero)
                {
                    if(b.zero && i == 0)
                    {
                        if(P_weight[curr][i]+1 < P_weight[next][i]) /* (V, +, +1) */
                        {
                            P_weight[next][i] = P_weight[curr][i]+1;
                            T[j+1][i] &= ~(15 << 0);
                            T[j+1][i] |= (9 << 0); /* 1001 */
                        }
                        if(N_weight[curr][i]+1 < N_weight[next][i]) /* (V, -, -1) */
                        {
                            N_weight[next][i] = N_weight[curr][i]+1;
                            T[j+1][i] &= ~(15 << 4);
                            T[j+1][i] |= (15 << 4); /* 1111 */
                        }
                    }
                    else
                    {
                        if(a.num.test(i) ^ b.num.test(i))
                        {
                            if(P_weight[curr][i]+1 < P_weight[next][i]) /* (V, +, +1) */
                            {
                                P_weight[next][i] = P_weight[curr][i]+1;
                                T[j+1][i] &= ~(15 << 0);
                                T[j+1][i] |= (9 << 0); /* 1001 */
                            }
                            if(N_weight[curr][i]+1 < N_weight[next][i]) /* (V, -, -1) */
                            {
                                N_weight[next][i] = N_weight[curr][i]+1;
                                T[j+1][i] &= ~(15 << 4);
                                T[j+1][i] |= (15 << 4); /* 1111 */
                            }
                        }
                        else
                        {
                            if(a.num.test(i) ^ a.num.test(i+1) ^ b.num.test(i+1))
                            {
                                if(P_weight[curr][i]+1 < N_weight[next][i]) /* (V, +, -1) */
                                {
                                    N_weight[next][i] = P_weight[curr][i]+1;
                                    T[j+1][i] &= ~(15 << 4);
                                    T[j+1][i] |= (11 << 4); /* 1011 */
                                }
                                if(N_weight[curr][i] < N_weight[next][i]) /* (V, -, 0) */
                                {
                                    N_weight[next][i] = N_weight[curr][i];
                                    T[j+1][i] &= ~(15 << 4);
                                    T[j+1][i] |= (12 << 4); /* 1100 */
                                }
                            }
                            else
                            {
                                if(P_weight[curr][i] < P_weight[next][i]) /* (V, +, 0) */
                                {
                                    P_weight[next][i] = P_weight[curr][i];
                                    T[j+1][i] &= ~(15 << 0);
                                    T[j+1][i] |= (8 << 0); /* 1000 */
                                }
                                if(N_weight[curr][i]+1 < P_weight[next][i]) /* (V, -, +1) */
                                {
                                    P_weight[next][i] = N_weight[curr][i]+1;
                                    T[j+1][i] &= ~(15 << 0);
                                    T[j+1][i] |= (13 << 0); /* 1101 */
                                }
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
    bool type = T[j][i] & (1 << 3);
    bool sign = T[j][i] & (1 << 2);
    bool change_sign = T[j][i] & (1 << 1);
    bool change_value = T[j][i] & (1 << 0);
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
        printf("\nUsage: %s some_integer\n\n", argv[0]);
        exit(1);
    }

    bigint_t n;
    str_to_bits(argv[1], &n);    
    chain_t shortest;
    
    auto start = std::chrono::steady_clock::now();
    optimal_chain(n, &shortest);
    auto end = std::chrono::steady_clock::now();

    std::cout << "# Time: ";
    std::cout << (std::chrono::duration_cast<std::chrono::microseconds>(end-start).count()) ;
    std::cout << " microseg" << std::endl;

    printf("# Minimum of %" PRIu64 "\n", shortest.weight);
    print_chain(&shortest);
    
	return 0;
}
