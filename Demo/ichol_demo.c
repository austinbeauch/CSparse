#include <time.h>
#include <stdio.h>
#include "cs.h"

#define calloc mxCalloc

// typedef struct DenseVector    /* matrix in compressed-column or triplet form */
// {
//     double *data;
//     int *index;
// } dense ;

typedef struct DenseVector
{
    double data;
    int index;
} dvec ;

// dense *vector_alloc(csi n){
//     dense *x = cs_calloc(1, sizeof(dense));
//     x->data = cs_malloc(n, sizeof(double));
//     x->index = cs_malloc(n, sizeof(csi));
//     for (size_t i = 0; i < n; i++) x->index[i] = i;
//     return x;
// }

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

void printv(dvec *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%0.2f ", arr[i].data);
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

int cmp(const void *a, const void *b)
{
    dvec *a1 = (dvec *)a;
    dvec *a2 = (dvec *)b;

    if(fabs(a1->data) < fabs(a2->data)) return 1;
    if(fabs(a2->data) > fabs(a2->data)) return -1;
    return 0;
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

    dvec* vec = malloc(n * sizeof *vec);

    csi maxvals = (n * (n+1) / 2) + (max_p * (n-max_p));
    L = cs_spalloc (n, n, maxvals, 1, 0); 
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    Lp[0] = 0;

    for (k = 0 ; k < n ; k++) { 

        for (i = 0 ; i < k ; i++) {
            vec[i].data = 0;
            vec[i].index = i;
        }

        // get dense kth upper column from A
        for (p = Ap [k] ; p < Ap [k+1] ; p++) {

            // store the kth diagonal value in A
            if (Ai[p] == k){
              Akk = Ax[p]; 
              break;
            } 
            if (Ai[p] > k) break;
            vec[Ai[p]].data = Ax[p];
        }

        // set current Cholesky factor
        L->x = Lx; L->i = Li; L->p = Lp; L->n = k; L->m = k;

        // triangular solve, solution on the output
        // start = clock();
        cs_utsolve_new(L, vec);
        // end = clock();
        // cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
        // printf("k=%li utsolve Time: %f\n", k, cpu_time_used);

        // find nonzeros from the solution vector x
        top = 0; l12 = 0;
        for (i = 0; i < k; i++){

            // threshold check
            if (fabs(vec[i].data) > t){ 
                // store nonzeros of x at the start of the array for future sorting
                vec[top].data = vec[i].data;
                vec[top++].index = vec[i].index;
            }
        }

        // sort data and indices so we can store row in Li
        qsort(vec, top, sizeof(dvec), cmp);
        // for (i=0; i<top; i++) printf("%f ", vec[i].data);
        // printf("\n");

        // store top entries in Lx and Li
        for (i = 0; i < max_p && i < top; i++){

            Lx[xcount++] = vec[i].data;
            l12 += vec[i].data * vec[i].data; // store dot product

            Li[icount++] = vec[i].index;
        }

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
    stdin = fopen("../Matrix/eu3_2_0", "rb+");
    // stdin = fopen("../Matrix/eu3_22_0", "rb+");
    // stdin = fopen("../Matrix/dense_rand", "rb+");
    // stdin = fopen("../Matrix/triplet_mat", "rb+");
    T = cs_load(stdin) ;
    A = cs_compress (T) ;              
    // cs_print (A, 0) ; /* print A */

    n = A->n ;
    printf("n = %li\n", n);

    // start = clock();
    // S = cs_schol (order, A) ;               /* ordering and symbolic analysis */
    // N = cs_chol (A, S) ;                    /* numeric Cholesky factorization */
    // printf ("chol(L):\n") ; cs_print (cs_transpose(N->L, 1), 0) ;
    // end = clock();
    // cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    // printf("chol CPU Time: %f\n", cpu_time_used);

    start = clock();
    // ichol(t, p)
    float t = 0;
    int p = n;
    L = cs_ichol(A, 0, n);
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("ichol CPU Time: %f\n", cpu_time_used);

    printf ("ichol(L, %e, %d):\n", t, p) ; cs_print (L, 0) ;
    // printf("n = %li\n", n);
    // printf ("N:\n") ; cs_print (N->L, 0) ; /* print A */
    // FILE *fptr;
    // fptr = fopen("out","w");
    // cs_save(N->L, fptr);
    // fclose(fptr);

    return (0) ;
}
