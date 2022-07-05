#include <time.h>
#include <stdio.h>
#include <string.h>
#include "cs.h"

#define MAX_INT 2147483647
#define noop

typedef struct DenseVector
{
    double data;
    int index;
} dvec ;

typedef struct PCGReturn
{
    double *x;
    double residual;
    csi iter;
} pcg_return;

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

pcg_return ichol_pcg(cs *A, double *b, cs *L, double tol, int max_iter){

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
    // Lc=r, output on vector c
    lsolve (L, r, c) ;

    // Lh = c, output on vector h
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
            pcg_return ret;
            ret.x = x;
            ret.iter = k;
            ret.residual = delta;
            return ret;
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

    // return PCGReturn struct
    pcg_return ret;
    ret.x = x;
    ret.iter = k;
    ret.residual = delta;

    return ret;
}

int main (int argc, char* argv[])
{

    // init file 
    FILE *fp, *outfile;

    outfile = fopen("chol_out", "wb+");
    fprintf(outfile, "type,t,p,iters,res,symb_time,flop_time,sol_time,tot_time\n");

    cs *T, *A, *L;
    css *S;
    csn *N;
    csi n, L_vals, iL_vals;

    float t = 0 ; float tol = 1e-6; 
    int max_iter = 100; int max_p=-1; 

    clock_t start, end;
    double tot_cpu_time, cpu_time_used;

    if (argc < 2) {
        printf("Usage: ./ichol_demo <matrix_file> [-t threshold] [-p max_row_nonzeros] [-tol tolerance] [-iter max_iterations]\n");
        return 0;
    }

    fp = fopen(argv[1], "rb+");
    T = cs_load(fp) ;
    A = cs_compress (T) ; 
    
    if (!A)
    {
        printf ("Input matrix is not found.\n") ;
        return (1) ;
    }

    n = A->n ;
    if (n == 0)
    {
        printf ("Error: matrix is empty\n") ;
        return (1) ;
    }

    for(int i = 1; i<argc; ++i)
    {   
        if (strcmp(argv[i], "-t") == 0)
            t = atof(argv[++i]);
        
        else if (strcmp(argv[i], "-p") == 0)
            max_p = atoi(argv[++i]);
        
        else if (strcmp(argv[i], "-tol") == 0)
            tol = atof(argv[++i]);
        
        else if (strcmp(argv[i], "-iter") == 0)
            max_iter = atoi(argv[++i]);
    }

    yellow(); printf("n = %li\n", n); reset();

    if (max_p == -1)
        max_p = n;

    // cs identity matrix, use for testing with no preconditioner
    cs *I = cs_spalloc (n, n, n, 1, 1) ;
    for (csi i = 0 ; i < n ; i++)
        cs_entry (I, i, i, 1) ;
    I = cs_compress (I) ;

    // create b such that solution x = 1
    double *b = cs_malloc (n, sizeof (double)) ;
    double *x = cs_malloc (n, sizeof (double)) ;
    pcg_return ret;
    for (csi i = 0 ; i < n ; i++){
        x[i] = 1;
        b[i] = 0;
    } 
    cs_gaxpy(A, x, b);

    double symb_fact, flop_fact, sol_fact, tot_fact=0;

    if (n > 1000)
    {
        // int gb = S->cp[n] * 32 / 8 / 1000000000;
        // printf ("Cholesky error, trying to allocate %d GB\n", gb) ;
        printf("Skipping full Cholesky factorization\n");
        fprintf(outfile, "chol,,,,,,,,\n");
    }
    else{
        red();
        printf("\nSolution with full Cholesky:\n");
        reset();
        start = clock();
        S = cs_schol (0, A) ;               
        end = clock();
        symb_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
        tot_fact += symb_fact;

        start = clock();
        N = cs_chol (A, S) ; 
        end = clock();
        flop_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
        tot_fact += flop_fact;

        start = clock();
        ret = ichol_pcg(A, b, N->L, tol, max_iter);
        end = clock();
        sol_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
        tot_fact += sol_fact;

        L_vals = N->L->p[n];
        printf("full chol + solve CPU Time: ");    
        green();
        printf("%f\n", cpu_time_used);
        reset(); 
        fprintf(outfile, "chol,,,%ld,%f,%f,%f,%f,%f\n", ret.iter, ret.residual, symb_fact, flop_fact, sol_fact, tot_fact);
    } 

    red();
    printf("\nSolution with CG:\n");
    reset();
    start = clock();
    ret = ichol_pcg(A, b, I, tol, max_iter);
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("CG CPU solve Time: ");
    green();
    printf("%f\n", cpu_time_used);
    reset();
    fprintf(outfile, "cg,,,%ld,%f,,,%f,%f\n", ret.iter, ret.residual, cpu_time_used, cpu_time_used);

    red();
    printf("\nSolution with PCG, ichol(t=%0.1e, p=%d):\n", t, max_p); 
    reset();
    cpu_time_used = 0;
    start = clock();     
    S = cs_schol (0, A) ;      
    end = clock();
    symb_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
    tot_cpu_time += symb_fact;
    printf("Time for symbolic factorization: %f\n", symb_fact);

    start = clock();
    L = cs_ichol (A, S, t, max_p);
    end = clock();
    flop_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
    tot_cpu_time += flop_fact;
    printf("Time for numeric computation: %f\n", flop_fact);

    start = clock();
    ret = ichol_pcg(A, b, L, tol, max_iter);                    
    end = clock();
    sol_fact = ((double) (end - start)) / CLOCKS_PER_SEC; 
    tot_cpu_time += sol_fact;
    printf("Time for solve: %f\n", sol_fact);
    printf("ichol(t=%0.3e, p=%d) + solve CPU Time: ", t, max_p);
    green();
    printf("%f\n", tot_cpu_time);
    reset();
    fprintf(outfile, "ichol,%0.3e,%d,%ld,%f,%f,%f,%f,%f\n", t, max_p, ret.iter, ret.residual, symb_fact, flop_fact, sol_fact, tot_cpu_time);

    fclose(fp);
    fclose(outfile);

    return (0) ;
}
