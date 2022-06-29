#include <time.h>
#include <stdio.h>
#include "cs.h"

#define noop

typedef struct DenseVector
{
    double data;
    int index;
} dvec ;

void print(double *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%0.2f ", arr[i]);
    }
    printf("\n");
}

void printi(csi *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%li ", arr[i]);
    }
    printf("\n");
}

void printv(dvec *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%0.2f (%d),  ", arr[i].data, arr[i].index);
    }
    printf("\n");
}

void printcs(cs *A, int num){
    printf("m=%ld, n=%ld\n", A->m, A->n);
    print(A->x, num);
    printi(A->i, num);
    printi(A->p, num);
}

int compare_values(const void *a, const void *b)
{
    dvec *a1 = (dvec *)a;
    dvec *a2 = (dvec *)b;

    if(fabs(a1->data) < fabs(a2->data)) return 1;
    if(fabs(a2->data) > fabs(a2->data)) return -1;
    return 0;
}

int compare_indices(const void *a, const void *b)
{
    dvec *a1 = (dvec *)a;
    dvec *a2 = (dvec *)b;

    if(a1->index > a2->index) return 1;
    if(a1->index < a2->index) return -1;
    return 0;
}


cs *cs_ichol (const cs *A, const css *S, float t, csi max_p)
{
    /*
        TODO: Add threshold to not add small values. ✅
        TODO: Insert triangular solve values into L. ✅
        TODO: Sort row entries to keep the top p elements. ✅
    */

    double total_reset_time=0, total_pattern_time=0;
    double d, lki, *Lx, *x, *Cx, curr_data;
    csi top, i, p, k, n, *Li, *Lp, *cp, *pinv, *s, *c, *parent, *Cp, *Ci;
    csi x_nnz, target_idx, curr_idx, *adds, flops=0;
    cs *L, *C, *U ;
    csn *N ;
    if (!CS_CSC (A) || !S || !S->cp || !S->parent){
        printf("Error: Invalid input.\n");
        return (NULL) ;
    } 
    n = A->n ;
    c = cs_malloc (2*n, sizeof (csi)) ;     /* get csi workspace */
    // x = cs_malloc (n, sizeof (double)) ;    /* get double workspace */
    cp = S->cp ; pinv = S->pinv ; parent = S->parent ;
    C = pinv ? cs_symperm (A, pinv, 1) : ((cs *) A) ;
    s = c + n ;
    Cp = C->p ; Ci = C->i ; Cx = C->x ;

    csi maxvals = (max_p * (max_p+1) / 2) + (max_p * (n-max_p));

    maxvals = maxvals > Cp[n] ? Cp[n] : maxvals;

    L = cs_spalloc (n, n, maxvals, 1, 0);
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    
    dvec *x_vec =    (dvec*)malloc(n*sizeof(dvec));
    dvec *nonzeros = (dvec*)malloc(n*sizeof(dvec));

    for (k = 0 ; k < n ; k++) {
        x_vec[k].data = 0   ; x_vec[k].index = k;
        nonzeros[k].data = 0; nonzeros[k].index = k;
        c [k] = cp [k] ; 
        Lp[k] = 0;
    }

    Lp[0] = 0; Lp[1] = 1;
    
    for (k = 0 ; k < n ; k++)       /* compute L(k,:) for L*L' = C */
    {        
        // printf("k = %ld\n", k);

        /* --- Nonzero pattern of L(k,:) ------------------------------------ */
        top = cs_ereach (C, k, parent, s, c) ;      /* find pattern of L(k,:) */
        x_vec[k].data = 0;                          /* x (0:k) is now zero */
        for (p = Cp [k] ; p < Cp [k+1] ; p++)       /* x = full(triu(C(:,k))) */
        {
            if (Ci [p] <= k) {
                x_vec[Ci[p]].data = Cx[p];
            }
        }

        d = x_vec[k].data ;                     /* d = C(k,k) */
        x_vec[k].data = 0;

        /* --- Triangular solve --------------------------------------------- */
        x_nnz = 0; 
        for ( ; top < n ; top++)    /* solve L(0:k-1,0:k-1) * x = C(:,k) */
        {
            i = s [top] ;           /* s [top..n-1] is pattern of L(k,:) */

            lki = x_vec[i].data / Lx [Lp [i]];
            
            x_vec[i].data = 0; 

            if (fabs(lki) < t) continue;  // skips flops if lki is below threshold

            nonzeros[x_nnz].data = lki;
            nonzeros[x_nnz++].index = i;

            for (p = Lp [i] + 1 ; p < Lp[i+1] ; p++){
                x_vec[Li [p]].data -= Lx [p] * lki;
            }

            d -= lki * lki ;            /* d = d - L(k,i)*L(k,i) */
        }

        if (d <= 0) {
            printf("Not positive definite\n");
            return NULL; 
        } 

        int keep_vals = x_nnz < max_p - 1 ? x_nnz : max_p - 1;

        // sort values if we have more than allowed to keep
        if (x_nnz > keep_vals){
            qsort(nonzeros, x_nnz, sizeof(dvec), compare_values);
        }

        qsort(nonzeros, keep_vals, sizeof(dvec), compare_indices);  // sort p by index to insert in order

        nonzeros[keep_vals].data = sqrt(d);
        nonzeros[keep_vals++].index = k;

        Lp[k + 1] = Lp[k];
        for (p = Lp[k]; p >= 0; p--){
            curr_idx  = nonzeros[keep_vals-1].index;
            curr_data = nonzeros[keep_vals-1].data;

            target_idx = Lp[ curr_idx +1 ];

            if (p == target_idx){
                
                // shift value in target position, in case something occupies that spot
                Lx[p + keep_vals] = Lx[p];
                Li[p + keep_vals] = Li[p];

                // insert the value
                Lx[p] = curr_data;
                Li[p] = k;

                // when we insert we need to shift ALL future column pointers.
                for (i = curr_idx+1; i <= k+1; i++) Lp[i]++;

                keep_vals--;
            }

            // shift values down by x_nnz
            Lx[p + keep_vals] = Lx[p];
            Li[p + keep_vals] = Li[p];

            // clear dense x vector
            nonzeros[keep_vals].data = 0;
            nonzeros[keep_vals].index = keep_vals; 

            if (p == target_idx) p++;
            if (keep_vals == 0) break;
        }

    }

    free(nonzeros);
    free(x_vec);
    free(c);
    return L;
}

int main (void)
{
    cs *T, *A, *L;
    css *S;
    csn *N;
    csi order, n;

    clock_t start, end;
    double cpu_time_used;

    // stdin = fopen("../Matrix/eu3_2_0", "rb+");
    // stdin = fopen("../Matrix/eu3_10_0", "rb+");
    // stdin = fopen("../Matrix/eu3_15_0", "rb+");
    // stdin = fopen("../Matrix/eu3_22_0", "rb+");
    // stdin = fopen("../Matrix/eu3_35_0", "rb+");
    // stdin = fopen("../Matrix/eu3_50_0", "rb+");
    stdin = fopen("../Matrix/eu3_100_0", "rb+");
    // stdin = fopen("../Matrix/triplet_mat", "rb+");
    // stdin = fopen("../Matrix/manual_8x8", "rb+");

    T = cs_load(stdin) ;
    A = cs_compress (T) ;              
    // cs_print (A, 0) ; /* print A */

    n = A->n ;
    printf("n = %li\n", n);

    S = cs_schol (0, A) ;               
    start = clock();
    N = cs_chol (A, S) ;                    /* numeric Cholesky factorization */
    // printf ("chol(L):\n") ; cs_print (cs_transpose(N->L, 1), 0) ;
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    // printf ("chol(L):\n") ; cs_print (N->L, 0) ;
    csi L_vals = N->L->p[n];
    printf("Total vals: %li\n", L_vals);
    printf("full chol CPU Time: %f\n\n", cpu_time_used);

    float t = 1e-4; int p = n;

    S = cs_schol (0, A) ;      
    start = clock();        
    L = cs_ichol (A, S, t, p) ;                    
    end = clock();
    csi iL_vals = L->p[n];
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    // printf ("chol(L):\n") ; cs_print (L, 0) ;
    printf("Total vals: %li\n", iL_vals);
    printf("Ratio of vals: %f\n", (float)iL_vals/L_vals);
    printf("ichol(t=%0.3e, p=%d) CPU Time: %f\n", t, p, cpu_time_used);

    return (0) ;
}
