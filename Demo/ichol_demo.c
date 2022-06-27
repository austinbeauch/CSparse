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
    if(a1->index < a2->index) return -1;
    return 0;
}

cs *add_spvec(cs *A, cs *B, float alpha, float beta){
    cs *C;
    double *Ax, *Bx, *Cx;
    csi *Ai, *Ap, *Bp, *Bi, *Cp, *Ci;
    int acount = 0, bcount = 0, ccount = 0;
    Bp = B->p ; Bi = B->i ; Bx = B->x ;
    Ap = A->p ; Ai = A->i ; Ax = A->x ;

    C = cs_spalloc (A->m, 1, A->m, 1, 0); 
    Cp = C->p ; Ci = C->i ; Cx = C->x ;

    while (acount < Ap[1] || bcount < Bp[1] )
    {

        if (acount == Ap[1])
        {
            Cx[ccount] = beta * Bx[bcount];
            Ci[ccount] = Bi[bcount];
            bcount ++;
        }
        else if (bcount == Bp[1])
        {
            Cx[ccount] = alpha * Ax[acount];
            Ci[ccount] = Ai[acount];
            acount ++;
        }

        else if (Ai[acount] == Bi[bcount])
        {
            Cx[ccount] = alpha * Ax[acount] +  beta * Bx[bcount];
            Ci[ccount] = Ai[acount];
            acount ++;
            bcount ++;
        }

        // I can't merge these two if statements with above and I don't know why
        else if (Ai[acount] < Bi[bcount])
        {
            Cx[ccount] = alpha * Ax[acount];
            Ci[ccount] = Ai[acount];
            acount ++;
        }

        else if (Bi[bcount] < Ai[acount])
        {
            Cx[ccount] = beta * Bx[bcount];
            Ci[ccount] = Bi[bcount];
            bcount ++;
        }
        
        ccount ++;
        
    }
    Cp[0] = 0; Cp[1] = ccount;

    return C ;
}

cs *cs_ichol_up (const cs *A, float t, csi max_p)
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

            // then sort the biggest p values by index for inserting into Lx/Li in order
            qsort(x_vec, keep_vals, sizeof(dvec), compare_indices);
        }

        // store x_nnz entries in Lx and Li
        for (i = 0; i < keep_vals; i++){
            Lx[xcount] = x_vec[i].data;
            Li[xcount++] = x_vec[i].index;

            // store dot product
            l12 += x_vec[i].data * x_vec[i].data; 
        }

        // compute diagonal entry in L
        if (Akk - l12 < 0){
            printf("Not positive definite\n");
            // TODO: free some stuff
            return L;
        }

        // store diagonal and update end column pointer
        Lx[xcount] = sqrt(Akk - l12);
        Li[xcount++] = k;
        Lp[pcount++] = Lp[pcount-1] + keep_vals + 1; // or just xcount?
    }

    L->n = A->n; L->m = A->n;
    // TODO: free some stuff as well
    return L;
}

cs *cs_ichol_left (const cs *A, float t, csi max_p)
{
    // printf("START\n");
    double *Lx, *Ax, *x, Akk, l12;
    csi x_nnz, i, p, k, n, *Li, *Lp, *Ap, *Ai, icount = 0, xcount = 0, pcount = 1 ;
    cs *L, *B, *C;
    if (!CS_CSC (A)) return (NULL) ;
    n = A->n ;
    Ap = A->p ; Ai = A->i ; Ax = A->x ;
    max_p = max_p < n ? max_p : n;
    csi maxvals = (max_p * (max_p+1) / 2) + (max_p * (n-max_p));

    L = cs_spalloc (n, n, maxvals, 1, 0); 
    Lp = L->p ; Li = L->i ; Lx = L->x ;
    Lp[0] = 0;

    dvec* b_vec = malloc(n * sizeof *b_vec);
    dvec* c_vec = malloc(n * sizeof *c_vec);

    csi bcount = 0, ccount = 0;

    for (k = 0 ; k < n ; k++) {        

        for (i = 0 ; i < n ; i++) {
            b_vec[i].data = 0;  b_vec[i].index = i;
            c_vec[i].data = 0;  c_vec[i].index = i;
        }

        // grab kth lower column from A
        for (p = Ap [k] ; p < Ap [k+1] ; p++) {
            if (Ai[p] < k) continue;
            b_vec[Ai[p]].data = Ax[p];
        }

        // find nonzero entries in the kth row of L
        for (int search_col = 0; search_col < k; search_col++){
            for (p = Lp [search_col] ; p < Lp [search_col+1] ; p++){
                if (Li[p] > k) break; // we're past the kth row with no entry, break

                else if (Li[p] == k) {
                    // we found an existing j
                    float L_jk = Lx[p];

                    // need to grab the rest of the column, downwards from p, store in vector C
                    ccount = 0;
                    for (int pp = p ; pp < Lp [search_col+1] ; pp++) {
                        // do multiplication with L_jk
                        c_vec[Li[pp]].data = Lx[pp] * L_jk;
                    }

                    // printf("k=%ld\n", k);
                    // B = add_vecs(b_vec, c_vec, 1, -1);
                    for (i = 0 ; i < n ; i++) {
                        b_vec[i].data -= c_vec[i].data;
                    }

                    // B = add_spvec(B, C, 1, -1);
                    break;
                }
            }
        }

        // put nonzero values at the front of the array
        x_nnz = 0; l12 = 0;
        for (i = 0; i < n; i++){
            if (fabs(b_vec[i].data) > t){ 
                b_vec[x_nnz].data = b_vec[i].data;
                b_vec[x_nnz++].index = b_vec[i].index;
            }
            if (x_nnz > max_p) break; // bad p implementation
            
        }

        float diag =  sqrt(b_vec[0].data);;
        // set diagonal
        Lx[xcount] = diag;
        Li[xcount++] = b_vec[0].index;

        // set the rest of the column
        for (i = 1; i < x_nnz; i++){
            Lx[xcount] = b_vec[i].data / diag;
            Li[xcount++] = b_vec[i].index;
        }

        Lp[pcount++] = xcount;

    }
    return L;
}

cs *cs_ichol (const cs *A, const css *S, float t, csi max_p)
{
    /*
        TODO: Add threshold to not add small values. ✅
        TODO: Insert triangular solve values into L. ✅
        TODO: Sort row entries to keep the top p elements. ✅
    */
   csi total_vals = 0;
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

        total_vals += keep_vals;

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

    printf("Total vals: %ld\n", total_vals);
    free(nonzeros);
    free(x_vec);
    free(c);
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
    // stdin = fopen("../Matrix/eu3_10_0", "rb+");
    // stdin = fopen("../Matrix/eu3_15_0", "rb+");
    // stdin = fopen("../Matrix/eu3_22_0", "rb+");
    // stdin = fopen("../Matrix/eu3_35_0", "rb+");
    // stdin = fopen("../Matrix/eu3_50_0", "rb+");
    // stdin = fopen("../Matrix/eu3_100_0", "rb+");
    // stdin = fopen("../Matrix/dense_rand", "rb+");
    stdin = fopen("../Matrix/triplet_mat", "rb+");
    // stdin = fopen("../Matrix/manual_8x8", "rb+");
    // stdin = fopen("../Matrix/A5x5", "rb+");    

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
    printf("Total vals: %li\n", N->L->p[n]);
    printf("full chol CPU Time: %f\n\n", cpu_time_used);

    float t = 1e-3; int p = n;

    S = cs_schol (0, A) ;      
    start = clock();        
    L = cs_ichol (A, S, t, p) ;                    
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;  
    // printf ("chol(L):\n") ; cs_print (L, 0) ;
    printf("ichol CPU Time: %f\n", cpu_time_used);

    // FILE *fptr;
    // fptr = fopen("out","w");
    // cs_save(N->L, fptr);
    // fclose(fptr);

    return (0) ;
}
