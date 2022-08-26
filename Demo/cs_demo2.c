#include "cs_demo.h"
/* cs_demo2: read a matrix and solve a linear system */
int main (int argc, char* argv[])
{
    FILE *fp;
    fp = fopen(argv[1], "rb+");
    problem *Prob = get_problem (fp, 1e-14) ;
    demo2 (Prob) ;
    free_problem (Prob) ;
    return (0) ;
}
