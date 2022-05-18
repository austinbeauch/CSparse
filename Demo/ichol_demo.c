#include <time.h>
#include <stdio.h>
#include "cs.h"

void print(double *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%0.2f ", arr[i]);
    }
    printf("\n");
}

void printi(csi *arr){
    for (int i = 0; i < 19; i++) {
        printf("%li ", arr[i]);
    }
    printf("\n");
}

int compare_function(const void *a,const void *b) {
    double *x = (double *) a;
    double *y = (double *) b;
    if (*x < *y) return 1;
    else if (*x > *y) return -1; return 0;
}

cs *cs_ichol (const cs *A, csi t, csi max_p)
{

    clock_t start, end;
    double cpu_time_used;

    double *Lx, *Ax, *x, Akk, l12;
    csi top, i, p, k, n, *Li, *Lp, *Ap, *Ai, icount = 0, xcount = 0, pcount = 1 ;
    cs *L ;
    if (!CS_CSC (A)) return (NULL) ;
    n = A->n ;
    Ap = A->p ; Ai = A->i ; Ax = A->x ;
    x = cs_malloc (n, sizeof (double)) ;    /* get double workspace */
    csi maxvals = (n * (n+1) / 2) + (max_p * (n-max_p));

    L = cs_spalloc (n, n, maxvals, 1, 0); 
    Lp = L->p ; Li = L->i ; Lx = L->x ;

    Lp[0] = 0;

    for (k = 0 ; k < n ; k++) { 

        for (i = 0 ; i < k ; i++) x[i] = 0;

        // get dense kth upper column from A
        for (p = Ap [k] ; p < Ap [k+1] ; p++) {

            // store the kth diagonal value in A
            if (Ai[p] == k){
              Akk = Ax[p]; 
              break;
            } 
            if (Ai[p] > k) break;
            x[Ai[p]] = Ax[p];
        }

        // set current Cholesky factor
        L->x = Lx; L->i = Li; L->p = Lp; L->n = k; L->m = k;

        // triangular solve, solution on the output
        start = clock();
        cs_utsolve(L, x);
        end = clock();
        cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
        // printf("k=%li utsolve Time: %f\n", k, cpu_time_used);

        // find nonzeros from the solution vector x
        top = 0; l12 = 0;
        for (i = 0; i < k; i++){

            // threshold check
            if (fabs(x[i]) > t){ 

                // store nonzeros of x at the start of the array for future sorting
                x[top++] = x[i]; 

                // store x[i] in Lx
                Lx[xcount++] = x[i];
                l12 += x[i] * x[i]; // store dot product

                // store i in Li, which we've allocated maxvals space
                Li[icount++] = i;
            }
            // if (top >= max_p) break; // bad way to impliment max number of nonzeros
        }

        // print(x, top);
        // qsort(x, top, sizeof(double), compare_function);
        // print(x, top);

        // for (i = 0; i < top; i++){
        //     Lx[xcount++] = x[i]; // store x[i] in Lx
        //     l12 += x[i] * x[i];  // store dot product
        // }

        // compute diagonal entry in L
        if (Akk - l12 < 0){
            printf("Not positive definite\n");
            // TODO: free some stuff
            return L;
        }

        Lx[xcount++] = sqrt(Akk - l12);
        Li[icount++] = k;
        Lp[pcount++] = Lp[pcount-1] + top + 1;

    }
    return L;
}

int main (void)
{
    cs *T, *A, *L;
    css *S ;
    csn *N ;
    csi order, n ;

    clock_t start, end;
    double cpu_time_used;

    FILE *fp;
    // stdin = fopen("../Matrix/eu3_2_0", "rb+");
    stdin = fopen("../Matrix/eu3_22_0", "rb+");
    // stdin = fopen("../Matrix/triplet_mat", "rb+");
    T = cs_load(stdin) ;
    A = cs_compress (T) ;              
    // cs_print (A, 0) ; /* print A */

    n = A->n ;
    printf("n = %li\n", n);

    // start = clock();
    // S = cs_schol (order, A) ;               /* ordering and symbolic analysis */
    // N = cs_chol (A, S) ;                    /* numeric Cholesky factorization */
    // end = clock();
    // cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    // printf("chol CPU Time: %f\n", cpu_time_used);

    start = clock();
    L = cs_ichol(A, 1e-3, 5);
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("ichol CPU Time: %f\n", cpu_time_used);

    // printf ("L:\n") ; cs_print (L, 0) ;
    // printf("n = %li\n", n);
    // printf ("N:\n") ; cs_print (N->L, 0) ; /* print A */
    // FILE *fptr;
    // fptr = fopen("out","w");
    // cs_save(N->L, fptr);
    // fclose(fptr);

    return (0) ;
}

