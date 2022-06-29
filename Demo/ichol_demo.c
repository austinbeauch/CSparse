#include <time.h>
#include <stdio.h>
#include "cs.h"

#define noop

typedef struct DenseVector
{
    double data;
    int index;
} dvec ;

void red(){
    printf("\033[1;31m");
}

void green(){
    printf("\033[1;32m");
}

void yellow(){
    printf("\033[1;33m");
}

void blue(){
    printf("\033[1;34m");
}

void reset(){
    printf("\033[0m");
}

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

    csi alloc_vals = maxvals > cp[n] ? cp[n] : maxvals;

    L = cs_spalloc (n, n, alloc_vals, 1, 0);
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

// Lx = b, output on vector x
csi lsolve (const cs *L, double *b, double *x)
{
    csi p, j, n, *Lp, *Li ;
    double *Lx ;
    if (!CS_CSC (L) || !x) return (0) ;                     /* check inputs */
    n = L->n ; Lp = L->p ; Li = L->i ; Lx = L->x ;

    // copy b into x
    for (j = 0 ; j < n ; j++) x [j] = b [j] ;

    for (j = 0 ; j < n ; j++)
    {
        x [j] /= Lx [Lp [j]] ;
        for (p = Lp [j]+1 ; p < Lp [j+1] ; p++)
        {
            x [Li [p]] -= Lx [p] * x [j] ;
        }
    }
    return (1) ;
}

// L^T x = b, output on vector x
csi ltsolve (const cs *L, double *b, double *x)
{
    csi p, j, n, *Lp, *Li ;
    double *Lx ;
    if (!CS_CSC (L) || !x) return (0) ;                     /* check inputs */
    n = L->n ; Lp = L->p ; Li = L->i ; Lx = L->x ;

    // copy b into x
    for (j = 0 ; j < n ; j++) x [j] = b [j] ;
    for (j = n-1 ; j >= 0 ; j--)
    {
        for (p = Lp [j]+1 ; p < Lp [j+1] ; p++)
        {
            x [j] -= Lx [p] * x [Li [p]] ;
        }
        x [j] /= Lx [Lp [j]] ;
    }
    return (1) ;
}

double* ichol_pcg(cs *A, double *b, cs *L, double tol, int max_iter){

    double *r, *z, *p, *x, *h, *s, *c, delta=0, delta0=0, delta_new=0, dot=0;
    csi i, k, n;

    n = A->n ;

    c = cs_malloc (n, sizeof (double)) ; // workspace variable for two step triangular solve
    r = cs_malloc (n, sizeof (double)) ;
    z = cs_malloc (n, sizeof (double)) ;
    p = cs_malloc (n, sizeof (double)) ;
    x = cs_malloc (n, sizeof (double)) ;
    h = cs_malloc (n, sizeof (double)) ;
    s = cs_malloc (n, sizeof (double)) ;

    // compute initial residual, set x0 to 0
    for (i = 0 ; i < n ; i++) {
        x[i] = 0;
        r[i] = 0;     
    }

    cs_gaxpy (A, x, r) ;                    // r += A*x 
    for (i = 0 ; i < n ; i++)               // r = b - A*x
        r [i] = b [i] - r [i] ;

    // compute z0, Mz = r -> z = M^{-1}r -> L^{-T} ( L^{-1} r_{k+1} )
    // TODO: change solves to output a new vector instead of copy onto dense vector
    lsolve (L, r, c) ;

    // TODO: check if this ltsolve solves as if the matrix was transposed
    ltsolve (L, c, h);

    // set delta to the dot product between r and h
    for (i = 0 ; i < n ; i++) 
        delta += r[i] * h[i];

    delta0 = delta;

    // copy h into p
    for (i = 0 ; i < n ; i++) p[i] = h[i];

    for (k = 0; k < max_iter; k++)
    {
        if (delta < tol * tol * delta0)
        {
            printf("Converged in %ld iterations, residual %0.3e\n", k, delta);
            free(c); free(r); free(z); free(p); free(h); free(s);
            return x;
        }   
        // zero s
        for (i = 0 ; i < n ; i++) s[i] = 0;
        cs_gaxpy(A, p, s);

        // compute alpha
        dot = 0;
        for (i = 0 ; i < n ; i++) dot += p[i] * s[i];
        double alpha = delta / dot;

        // update x
        for (i = 0 ; i < n ; i++) x[i] += alpha * p[i];

        // update r
        for (i = 0 ; i < n ; i++) r[i] -= alpha * s[i];

        // compute h
        lsolve (L, r, c);
        ltsolve (L, c, h);

        // compute delta
        delta_new = 0;
        for (i = 0 ; i < n ; i++) delta_new += r[i] * h[i];

        // update p
        for (i = 0 ; i < n ; i++) p[i] = h[i] + delta_new / delta * p[i];
        delta = delta_new;
    }

    printf("Did not converge in %ld iterations, residual %0.3e\n", k, delta);
    free(c); free(r); free(z); free(p); free(h); free(s);
    return x;
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
    stdin = fopen("../Matrix/eu3_50_0", "rb+");
    // stdin = fopen("../Matrix/eu3_100_0", "rb+");
    // stdin = fopen("../Matrix/triplet_mat", "rb+");
    // stdin = fopen("../Matrix/manual_8x8", "rb+");

    T = cs_load(stdin) ;
    A = cs_compress (T) ;              
    // cs_print (A, 0) ; /* print A */

    n = A->n ;
    yellow();
    printf("n = %li\n", n);
    reset();

    // cs identity matrix, use for testing with no preconditioner
    cs *I = cs_spalloc (n, n, n, 1, 1) ;
    for (csi i = 0 ; i < n ; i++)
        cs_entry (I, i, i, 1) ;
    I = cs_compress (I) ;

    // create b such that solution x = 1
    double *b = cs_malloc (n, sizeof (double)) ;
    double *x = cs_malloc (n, sizeof (double)) ;
    double *sol;
    for (csi i = 0 ; i < n ; i++){
        x[i] = 1;
        b[i] = 0;
    } 
    cs_gaxpy(A, x, b);

    csi max_it = 1000; double tol = 1e-6;

    red();
    printf("\nSolution with full Cholesky:\n");
    reset();
    S = cs_schol (0, A) ;               
    start = clock();
    N = cs_chol (A, S) ;                    
    sol = ichol_pcg(A, b, N->L, tol, max_it);
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  

    csi L_vals = N->L->p[n];
    printf("Total vals: %li\n", L_vals);
    // l2 norm between sol and x
    printf("full chol + solve CPU Time: ");    
    green();
    printf("%f\n", cpu_time_used);
    reset();  

    red();
    printf("\nSolution with CG:\n");
    reset();
    start = clock();
    sol = ichol_pcg(A, b, I, tol, max_it);
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("CG CPU solve Time: ");
    green();
    printf("%f\n", cpu_time_used);
    reset();

    float t = 1e-2; int p = 10;

    red();
    printf("\nSolution with PCG, ichol(t=%0.1e, p=%d):\n", t, p); 
    reset();
    S = cs_schol (0, A) ;      
    start = clock();        
    L = cs_ichol (A, S, t, p) ;
    sol = ichol_pcg(A, b, L, tol, max_it);                    
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC; 
    csi iL_vals = L->p[n];
    
    printf("Total vals: %li, ratio: %f\n", iL_vals, (float)iL_vals/L_vals);
    printf("ichol(t=%0.3e, p=%d) + solve CPU Time: ", t, p);
    green();
    printf("%f\n", cpu_time_used);
    reset();

    return (0) ;
}
