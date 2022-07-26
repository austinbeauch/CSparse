#include <time.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h> 
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

//print boolean array
void printb(bool *arr, int num){
    for (int i = 0; i < num; i++) {
        printf("%d ", arr[i]);
    }
    printf("\n");
}

int cmpfunc (const void * a, const void * b) {
   return ( *(int*)a - *(int*)b );
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

cs *jones_ichol (const cs *A, float relative_thresh)
{

    double *Lx, *Ax, *d, *r, *a;
    double L_ij, L_jk, L_ik;
    bool *b;
    csi *Li, *Lp, *Ap, *Ai, *s, *t, *l, *c;
    csi p, i, j, k, n, c_n, k0, k1, k2, nnz;
    cs *L;
    n = A->n ;

    c_n = 0;
    nnz = 0;

    // calloc for s
    s = cs_calloc (n, sizeof (csi)) ; 
    t = cs_calloc (n, sizeof (csi)) ;
    c = cs_calloc (n, sizeof (csi)) ;
    l = cs_calloc (n, sizeof (csi)) ;
    a = cs_calloc (n, sizeof (double)) ;
    r = cs_calloc (n, sizeof (double)) ;
    d = cs_calloc (n, sizeof (double)) ;
    b = cs_calloc (n, sizeof (bool)) ;

    for (i = 0 ; i < n ; i++) {
        s [i] = 0 ;
        t [i] = 0 ;
        c [i] = 0 ;
        l [i] = -1 ;
        a [i] = 0 ;
        r [i] = 0 ;
        d [i] = 0 ;
        b [i] = false ;
    }

    Ap = A->p ; Ai = A->i ; Ax = A->x ;

    csi alloc_vals = 2e9/8; // set max allocation to 2GB
    L = cs_spalloc (n, n, alloc_vals, 1, 0);
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    
    // store diagonals in d, keep track of first sub-diagonal index in t, sum values in column j in r
    for (j = 0 ; j < n ; j++)
    {
        for (p = Ap [j] ; p < Ap [j+1] ; p++)
        {
            i = Ai[p];
            if (i == j)
            {
                d[j] += Ax[p];
                t[j] = p + 1;
            }
            if (i >= j)
            {
                r[j] += fabs(Ax[p]);
            }
        }
    }

    for (j = 0 ; j < n ; j++)
    {
        // for each L_ij on subdiagonal       
        for (p = t[j] ; p < Ap [j+1] ; p++){
            i = Ai[p];
            L_ij = Ax[p];
            if (L_ij != 0 && i > j)
            {
                a[i] = L_ij;
                if (b[i] == false){
                    b[i] = true;
                    c[c_n++] = i;
                }
            }
        }

        k = l[j];
        while (k != -1)
        {
            k0 = s[k];
            k1 = Lp[k+1];
            k2 = l[k];
            L_jk = Lx[k0++];
            if (k0 < k1){
                s[k] = k0;
                i = Li[k0];
                l[k] = l[i];
                l[i] = k;
                for (csi idx = k0; idx < k1; idx++)
                {
                    i = Li[idx];
                    L_ik = Lx[idx];
                    a[i] -= L_ik * L_jk;
                    if (b[i] == false){
                        b[i] = true;
                        c[c_n++] = i;
                    }
                }   
            }
            k = k2;
        }

        if (d[j] <= 0)
        {
            yellow();
            printf("Matrix is not positive definite.\n");
            reset();
            return NULL;
        }
        
        d[j] = sqrt(d[j]);
        Lx[nnz] = d[j];
        Li[nnz] = j;
        nnz++;
        s[j] = nnz;

        // Sort row indices of column j for correct insertion order into L
        qsort(c, c_n, sizeof(double), cmpfunc);

        for (k = 0 ; k < c_n ; k++)
        {
            i = c[k];
            L_ij = a[i] / d[j];
            if (true) d[i] -= L_ij * L_ij;

            float rel = relative_thresh * r[j];

            // if (fabs(a[i]) > rel)
            if (fabs(L_ij) > relative_thresh)
            {
                Lx[nnz] = L_ij;
                Li[nnz] = i;
                nnz++;
            }

            a[i] = 0;
            b[i] = false;
        }

        c_n = 0;
        Lp[j+1] = nnz;

        if (Lp[j] + 1 < Lp[j+1]) // if column j has a nonzero element below the diagonal
        {
            i = Li[Lp[j] + 1];
            l[j] = l[i];
            l[i] = j;
        }
    }
    return L;
}

cs *jones_icholtp(const cs *A, float relative_thresh, csi max_p)
{

    double *Lx, *Ax, *d, *r, *a;
    double L_ij, L_jk, L_ik;
    bool *b;
    csi *Li, *Lp, *Ap, *Ai, *s, *t, *l, *c;
    csi p, i, j, k, n, c_n, k0, k1, k2, nnz;
    cs *L;
    n = A->n ;

    c_n = 0;
    nnz = 0;

    // calloc for s
    s = cs_calloc (n, sizeof (csi)) ; 
    t = cs_calloc (n, sizeof (csi)) ;
    c = cs_calloc (n, sizeof (csi)) ;
    l = cs_calloc (n, sizeof (csi)) ;
    a = cs_calloc (n, sizeof (double)) ;
    r = cs_calloc (n, sizeof (double)) ;
    d = cs_calloc (n, sizeof (double)) ;
    b = cs_calloc (n, sizeof (bool)) ;

    dvec *x_vec = (dvec*)malloc(n*sizeof(dvec));
    dvec *from_a = (dvec*)malloc(n*sizeof(dvec));

    for (i = 0 ; i < n ; i++) {
        s [i] = 0 ;
        t [i] = 0 ;
        c [i] = 0 ;
        l [i] = -1 ;
        a [i] = 0 ;
        r [i] = 0 ;
        d [i] = 0 ;
        b [i] = false ;
        x_vec[i].data = 0;
        x_vec[i].index = i;
        from_a[i].data = 0;
        from_a[i].index = 0;
    }

    Ap = A->p ; Ai = A->i ; Ax = A->x ;

    // csi maxvals = (max_p * (max_p+1) / 2) + (max_p * (n-max_p));

    //             tril(A)         max_p extra  diag
    csi maxvals = (Ap[n] - n) / 2 + n * max_p + n;

    // values * 8 bytes per double, divide by a giga to get gigabytes
    double gb = maxvals * 8 / 1e9;

    // only allow 2gb of memory to be allocated
    if (gb > 2)
    {
        yellow();
        printf("Input p results in more than 2GB memory, setting max allocation to 2GB.\n");
        reset();
    }
    csi alloc_vals = gb > 2 ? 2e9/8 : maxvals;

    L = cs_spalloc (n, n, alloc_vals, 1, 0);
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    Lp[0] = 0;
    
    // store diagonals in d, keep track of first sub-diagonal index in t, sum values in column j in r
    for (j = 0 ; j < n ; j++)
    {
        for (p = Ap [j] ; p < Ap [j+1] ; p++)
        {
            i = Ai[p];
            if (i == j)
            {
                d[j] += Ax[p];
                t[j] = p + 1;
            }
            if (i >= j)
            {
                r[j] += fabs(Ax[p]);
            }
        }
    }

    for (j = 0 ; j < n ; j++)
    {
        // for each L_ij on subdiagonal       
        for (p = t[j] ; p < Ap [j+1] ; p++){
            i = Ai[p];
            L_ij = Ax[p];
            if (L_ij != 0 && i > j)
            {
                a[i] = L_ij;
                if (b[i] == false){
                    b[i] = true;
                    c[c_n++] = i;
                }
            }
        }

        k = l[j];
        while (k != -1)
        {
            k0 = s[k];
            k1 = Lp[k+1];
            k2 = l[k];
            L_jk = Lx[k0++];
            if (k0 < k1){
                s[k] = k0;
                i = Li[k0];
                l[k] = l[i];
                l[i] = k;
                for (csi idx = k0; idx < k1; idx++)
                {
                    i = Li[idx];
                    L_ik = Lx[idx];
                    a[i] -= L_ik * L_jk;
                    if (b[i] == false){
                        b[i] = true;
                        c[c_n++] = i;
                    }
                }   
            }
            k = k2;
        }

        if (d[j] <= 0)
        {
            yellow();
            printf("Matrix is not positive definite.\n");
            reset();
            return NULL;
        }
        
        d[j] = sqrt(d[j]);
        Lx[nnz] = d[j];
        Li[nnz] = j;
        nnz++;
        s[j] = nnz;

        // ----- Keep an extra p elements on top of a_ij != 0
        // copy a and c into x_vec
        for (i = 0; i < c_n; i++)
        {
            x_vec[c[i]].data = a[c[i]];
            x_vec[c[i]].index = c[i];
        }

        csi n_fill = c_n;
        csi a_count = 0;
        // get elements where a is nonzero
        for (p = t [j] ; p < Ap [j+1]; p++){
            i = Ai[p];
            from_a[a_count].data = a[i]; // store in from_a
            from_a[a_count++].index = i;

            a[i] = 0;
            b[i] = false;

            x_vec[i].data = 0; // remove it from x_vec
            n_fill--;
        }

        // keep an extra p elements
        int keep_vals = max_p; 
        
        int kept = n_fill < keep_vals ? n_fill : keep_vals;
        kept += a_count;
        
        if (n_fill > 0){
            // sort values if we have more than allowed to keep
            if (n_fill >= keep_vals){
                qsort(x_vec, n, sizeof(dvec), compare_values);
            } 

            // move fill back into from_a
            for (i = 0; i < n; i++)
            {
                if (i < keep_vals && fabs(x_vec[i].data) > 0){
                    from_a[a_count].data = x_vec[i].data;
                    from_a[a_count++].index = x_vec[i].index;
                }

                a[x_vec[i].index] = 0;
                b[x_vec[i].index] = false;

                x_vec[i].data = 0;
                x_vec[i].index = i;
            }

        }
        
        // Sort row indices of column j for correct insertion order into L
        qsort(from_a, a_count, sizeof(dvec), compare_indices);

        for (k = 0 ; k < kept ; k++)
        {
            i = from_a[k].index;
            L_ij = from_a[k].data / d[j];
            if (true) d[i] -= L_ij * L_ij;
            // float rel = relative_thresh * r[j];
            if (fabs(L_ij) > relative_thresh)
            {
                Lx[nnz] = L_ij;
                Li[nnz] = i;
                nnz++;
            }
        }

        c_n = 0;
        Lp[j+1] = nnz;

        if (Lp[j] + 1 < Lp[j+1]) // if column j has a nonzero element below the diagonal
        {
            i = Li[Lp[j] + 1]; // Row index of first off-diagonal non-zero element
            l[j] = l[i];       // Remember old list i index in list j
            l[i] = j;          // Insert index of non-zero element into list i
        }
    }
    return L;
}

int main (int argc, char* argv[])
{
    FILE *fp, *outfile;

    outfile = fopen("chol_out", "wb+");
    fprintf(outfile, "type,t,p,iters,res,symb_time,flop_time,sol_time,tot_time\n");

    cs *T, *A, *L;
    css *S;
    csn *N;
    csi n, L_vals, iL_vals;

    float t = -1; float tol = 1e-6; 
    int max_iter = 1000; int max_p = -1; 

    clock_t start, end;
    double symb_fact, flop_fact, sol_fact, tot_fact=0;;

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

    // -------------- FULL CHOLESKY -------------- //
    if (n > 1000)
    {
        // int gb = S->cp[n] * 32 / 8 / 1000000000;
        // printf ("Cholesky error, trying to allocate %d GB\n", gb) ;
        printf("Skipping full Cholesky factorization\n");
        // fprintf(outfile, "chol,,,,,,,,\n");
    }
    else
    {
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
        printf("%f\n", tot_fact);
        reset(); 
        fprintf(outfile, "chol,,,%ld,%f,%f,%f,%f,%f\n", ret.iter, ret.residual, symb_fact, flop_fact, sol_fact, tot_fact);
    } 

    // -------------- CG -------------- //
    // if not t, don't precondition
    if (t == -1 && max_p == -1)
    {
        tot_fact = 0;
        red();
        printf("\nSolution with CG (no preconditioning):\n");
        reset();
        start = clock();
        ret = ichol_pcg(A, b, I, tol, max_iter);
        end = clock();
        tot_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
        printf("CG CPU solve Time: ");
        green();
        printf("%f\n", tot_fact);
        reset();
        fprintf(outfile, "cg,,,%ld,%0.3e,,,%f,%f\n", ret.iter, ret.residual, tot_fact, tot_fact);
    }

    // -------------- ICHOL -------------- //
    if (t != -1 && max_p == -1)
    {
        // -------------- JONES -------------- //
        tot_fact = 0;
        red();
        printf("\nSolution with PCG, jones(t=%0.1e):\n", t); 
        reset();
        start = clock();  
        L = jones_ichol(A, t);
        end = clock();
        flop_fact = (double)(end - start) / CLOCKS_PER_SEC;
        tot_fact += flop_fact;
        printf("Time for Jones factorization: %f\n", flop_fact);
        printf("Nonzeros in L: %ld\n", L->p[n]);

        start = clock();
        ret = ichol_pcg(A, b, L, tol, max_iter);                    
        end = clock();
        sol_fact = ((double) (end - start)) / CLOCKS_PER_SEC; 
        tot_fact += sol_fact;
        printf("Time for solve: %f\n", sol_fact);
        printf("jones ichol(t=%0.3e) + solve CPU Time: ", t);
        green();
        printf("%f\n", tot_fact);
        reset();
        fprintf(outfile, "jones,%0.3e,,%ld,%0.3e,,%f,%f,%f\n", t, ret.iter, ret.residual, flop_fact, sol_fact, tot_fact);
    }
    
    else if (max_p != -1)

    {
        if (max_p == -1)
            max_p = n;

        if (t == -1)
            t = 0;
        
        if (n < 100000)
        {
            // -------------- BAD -------------- //
            tot_fact = 0;
            red();
            printf("\nSolution with PCG, ichol(t=%0.1e, p=%d):\n", t, max_p); 
            reset();
            start = clock();     
            S = cs_schol (0, A) ;      
            end = clock();
            symb_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
            tot_fact += symb_fact;
            double gb = S->cp[n] * 64 / 8 / 1000000000;
            printf ("Full Cholesky would have %ld nnz, or %0.2f GB\n", S->cp[n], gb) ;
            printf("Time for symbolic factorization: %f\n", symb_fact);

            start = clock();
            L = cs_ichol (A, S, t, max_p);
            end = clock();
            flop_fact = ((double) (end - start)) / CLOCKS_PER_SEC;
            tot_fact += flop_fact;
            printf("Time for numeric computation: %f\n", flop_fact);
            printf("Nonzeros in L: %ld\n", L->p[n]);

            start = clock();
            ret = ichol_pcg(A, b, L, tol, max_iter);                    
            end = clock();
            sol_fact = ((double) (end - start)) / CLOCKS_PER_SEC; 
            tot_fact += sol_fact;
            printf("Time for solve: %f\n", sol_fact);
            printf("ichol(t=%0.3e, p=%d) + solve CPU Time: ", t, max_p);
            green();
            printf("%f\n", tot_fact);
            reset();
            fprintf(outfile, "ichol,%0.3e,%d,%ld,%0.3e,%f,%f,%f,%f\n", t, max_p, ret.iter, ret.residual, symb_fact, flop_fact, sol_fact, tot_fact);

        }
        else {
            printf("Skipping bad ichol because n = %ld > 100000\n", n);
        }


        // -------------- MODIFIED JONES -------------- //
        tot_fact = 0;
        red();
        printf("\nSolution with PCG, modified jones(t=%0.1e, p=%d):\n", t, max_p); 
        reset();
        start = clock();  
        L = jones_icholtp(A, t, max_p);
        end = clock();
        flop_fact = (double)(end - start) / CLOCKS_PER_SEC;
        tot_fact += flop_fact;
        printf("Time for Jones factorization: %f\n", flop_fact);
        printf("Nonzeros in L: %ld\n", L->p[n]);

        start = clock();
        ret = ichol_pcg(A, b, L, tol, max_iter);                    
        end = clock();
        sol_fact = ((double) (end - start)) / CLOCKS_PER_SEC; 
        tot_fact += sol_fact;
        printf("Time for solve: %f\n", sol_fact);
        printf("modified jones ichol(t=%0.3e, p=%d) + solve CPU Time: ", t, max_p);
        green();
        printf("%f\n", tot_fact);
        reset();
        fprintf(outfile, "jones_tp,%0.3e,%d,%ld,%0.3e,,%f,%f,%f\n", t, max_p, ret.iter, ret.residual, flop_fact, sol_fact, tot_fact);

        //write the L matrix to a file
        // FILE *L_file = fopen("L.txt", "w");
        // for (csi i = 0; i < n; i++)
        // {
        //     for (csi j = L->p[i]; j < L->p[i+1]; j++)
        //     {
        //         fprintf(L_file, "%0.3e ", L->x[j]);
        //     }
        // }
        // fclose(L_file);
    }
    
    fclose(fp);
    fclose(outfile);

    return (0) ;
}
