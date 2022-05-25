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

csi cs_utsolve_new (const cs *U, dvec *x)
{
    csi p, j, n, *Up, *Ui ;
    double *Ux ;
    if (!CS_CSC (U) || !x) return (0) ; 
    n = U->n ; Up = U->p ; Ui = U->i ; Ux = U->x ;
    for (j = 0 ; j < n ; j++)
    {
        for (p = Up [j] ; p < Up [j+1]-1 ; p++)
        {
            x[j].data -= Ux [p] * x[Ui[p]].data ;
        }
        x[j].data /= Ux [Up [j+1]-1] ;
    }
    return (1) ;
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
    if(a2->index < a2->index) return -1;
    return 0;
}

cs *cs_ichol (const cs *A, float t, csi max_p)
{

    clock_t start, end;
    double cpu_time_used;

    double *Lx, *Ax, *x, Akk, l12;
    csi x_nnz, i, p, k, n, *Li, *Lp, *Ap, *Ai, icount = 0, xcount = 0, pcount = 1 ;
    cs *L ;
    if (!CS_CSC (A)) return (NULL) ;
    n = A->n ;
    Ap = A->p ; Ai = A->i ; Ax = A->x ;

    dvec* x_vec = malloc(n * sizeof *x_vec);

    max_p = max_p < n ? max_p : n;

    csi maxvals = (max_p * (max_p+1) / 2) + (max_p * (n-max_p));

    L = cs_spalloc (n, n, maxvals, 1, 0); 
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    Lp[0] = 0;

    for (i=0; i<maxvals; i++) Li[i] = -1;

    for (k = 0 ; k < n ; k++) { 

        for (i = 0 ; i < k ; i++) {
            x_vec[i].data = 0;
            x_vec[i].index = i;
        }

        // get dense kth upper column from A
        for (p = Ap [k] ; p < Ap [k+1] ; p++) {

            // store the kth diagonal value in A
            if (Ai[p] == k){
              Akk = Ax[p]; 
              break;
            } 
            if (Ai[p] > k) break;
            x_vec[Ai[p]].data = Ax[p];
        }

        // set current Cholesky factor
        L->x = Lx; L->i = Li; L->p = Lp; L->n = k; L->m = k;

        // triangular solve, solution on the output
        cs_utsolve_new(L, x_vec);

        // find nonzeros from the solution vector x
        x_nnz = 0; l12 = 0;
        for (i = 0; i < k; i++){

            // threshold check
            if (fabs(x_vec[i].data) > t){ 
                // store nonzeros of x at the start of the array for future sorting
                x_vec[x_nnz].data = x_vec[i].data;
                x_vec[x_nnz++].index = x_vec[i].index;
            }
        }

        int keep_vals = x_nnz < max_p - 1 ? x_nnz : max_p - 1;

        // sort values if we have more than allowed to keep
        if (x_nnz > keep_vals){

            // first sort all values
            qsort(x_vec, x_nnz, sizeof(dvec), compare_values);

            // then sort the x_nnz p by index for inserting into Lx/Li in order
            qsort(x_vec, keep_vals, sizeof(dvec), compare_indices);
        }

        // store x_nnz entries in Lx and Li
        for (i = 0; i < keep_vals; i++){
            Lx[xcount] = x_vec[i].data;
            l12 += x_vec[i].data * x_vec[i].data; // store dot product
            Li[xcount++] = x_vec[i].index;
        }

        // compute diagonal entry in L
        if (Akk - l12 < 0){
            printf("Not positive definite\n");
            // TODO: free some stuff
            return L;
        }

        Lx[xcount] = sqrt(Akk - l12);
        Li[xcount++] = k;
        Lp[pcount++] = Lp[pcount-1] + keep_vals + 1;

    }

    L->n = A->n; L->m = A->n;
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
    // stdin = fopen("../Matrix/eu3_22_0", "rb+");
    // stdin = fopen("../Matrix/dense_rand", "rb+");
    // stdin = fopen("../Matrix/triplet_mat", "rb+");
    stdin = fopen("../Matrix/manual_8x8", "rb+");
    T = cs_load(stdin) ;
    A = cs_compress (T) ;              
    // cs_print (A, 0) ; /* print A */

    n = A->n ;
    printf("n = %li\n", n);

    start = clock();
    S = cs_schol (order, A) ;               /* ordering and symbolic analysis */
    N = cs_chol (A, S) ;                    /* numeric Cholesky factorization */
    // printf ("chol(L):\n") ; cs_print (cs_transpose(N->L, 1), 0) ;
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    printf("chol CPU Time: %f\n", cpu_time_used);

    start = clock();
    float t = 0.2; int p = 4;
    L = cs_ichol(A, t, p);
    printf ("ichol(L, %e, %d):\n", t, p) ; cs_print (L, 0) ;
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("ichol CPU Time: %f\n", cpu_time_used);

    // printf ("ichol(L, %e, %d):\n", t, p) ; cs_print (L, 0) ;

    // FILE *fptr;
    // fptr = fopen("out","w");
    // cs_save(N->L, fptr);
    // fclose(fptr);

    return (0) ;
}
