/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko
// Modified to be easier to use in pipe chains by Tobias Boege <tboege@ovgu.de> 2018

#include "solver.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <time.h>
#include <limits.h>
#include <err.h>
//#include <unistd.h>
#include <signal.h>
//#include <zlib.h>
//#include <sys/time.h>
//#include <sys/resource.h>

#ifdef GMP
#include <gmp.h>
#endif

#include "main.h"

//=================================================================================================
// Helpers:

/* printf but for diagnostics */
int diag(char *fmt, ...)
{
	va_list args;
	int res;

	va_start(args, fmt);
	res = vfprintf(stderr, fmt, args);
	va_end(args);
	return res;
}

// Reads an input stream to end-of-file and returns the result as a 'char*' terminated by '\0'
// (dynamic allocation in case 'in' is standard input).
//
char* readFile(FILE *  in)
{
    char*   data = malloc(65536);
    int     cap  = 65536;
    int     size = 0;

    while (!feof(in)){
        if (size == cap){
            cap *= 2;
            data = realloc(data, cap); }
        size += fread(&data[size], 1, 65536, in);
    }
    data = realloc(data, size+1);
    data[size] = '\0';

    return data;
}

//static inline double cpuTime(void) {
//    struct rusage ru;
//    getrusage(RUSAGE_SELF, &ru);
//    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }


//=================================================================================================
// DIMACS Parser:


static inline void skipWhitespace(char** in) {
    while ((**in >= 9 && **in <= 13) || **in == 32)
        (*in)++; }

static inline void skipLine(char** in) {
    for (;;){
        if (**in == 0) return;
        if (**in == '\n') { (*in)++; return; }
        (*in)++; } }

static inline int parseInt(char** in) {
    int     val = 0;
    int    _neg = 0;
    skipWhitespace(in);
    if      (**in == '-') _neg = 1, (*in)++;
    else if (**in == '+') (*in)++;
    if (**in < '0' || **in > '9') warn("PARSE ERROR! Unexpected char: %c\n", **in), exit(1);
    while (**in >= '0' && **in <= '9')
        val = val*10 + (**in - '0'),
        (*in)++;
    return _neg ? -val : val; }

static void readClause(char** in, solver* s, veci* lits) {
    int parsed_lit, var;
    veci_resize(lits,0);
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        veci_push(lits, (parsed_lit > 0 ? toLit(var) : lit_neg(toLit(var))));
    }
}

static lbool parse_DIMACS_main(char* in, solver* s) {
    veci lits;
    veci_new(&lits);

    for (;;){
        skipWhitespace(&in);
        if (*in == 0)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(&in);
        else{
            lit* begin;
            readClause(&in, s, &lits);
            begin = veci_begin(&lits);
            if (!solver_addclause(s, begin, begin+veci_size(&lits))){
                veci_delete(&lits);
                return l_False;
            }
        }
    }
    veci_delete(&lits);
    return solver_simplify(s);
}


// Inserts problem into solver. Returns FALSE upon immediate conflict.
//
static lbool parse_DIMACS(FILE * in, solver* s) {
    char* text = readFile(in);
    lbool ret  = parse_DIMACS_main(text, s);
    free(text);
    return ret; }


//=================================================================================================


void printStats(stats* stats, unsigned long cpu_time, bool interrupted)
{
    double Time    = (double)(cpu_time)/(double)(CLOCKS_PER_SEC);
    diag("restarts          : %12llu\n", stats->starts);
    diag("conflicts         : %12.0f           (%9.0f / sec      )\n",  (double)stats->conflicts   , (double)stats->conflicts   /Time);
    diag("decisions         : %12.0f           (%9.0f / sec      )\n",  (double)stats->decisions   , (double)stats->decisions   /Time);
    diag("propagations      : %12.0f           (%9.0f / sec      )\n",  (double)stats->propagations, (double)stats->propagations/Time);
    diag("inspects          : %12.0f           (%9.0f / sec      )\n",  (double)stats->inspects    , (double)stats->inspects    /Time);
    diag("conflict literals : %12.0f           (%9.2f %% deleted  )\n", (double)stats->tot_literals, (double)(stats->max_literals - stats->tot_literals) * 100.0 / (double)stats->max_literals);
    diag("CPU time          : %12.2f sec\t", Time);
    diag("\n");

#ifdef NONDISJOINT
    diag("disjoint          : disabled\n");
#else
    diag("disjoint          : enabled\n");
#endif

#ifdef FIXEDORDER
    diag("variable ordering : fixed\n");
#else
    diag("variable ordering : heuristic\n");
#endif

#ifdef CONTINUE
    diag("continuation      : enabled\n");
#else
    diag("continuation      : disabled\n");
#endif

#ifdef GMP
    diag("gmp               : enabled\n");
#ifdef SIMPLIFY
    diag("simplification    : enabled\n");
    diag("SAT (partial)     : ");
    mpz_out_str(stdout, 10, stats->par_solutions);
    if (interrupted)
        diag("+");
    diag("\n");

#ifndef NONDISJOINT
    diag("SAT (full)        : ");
    mpz_out_str(stdout, 10, stats->tot_solutions);
    if (interrupted)
        diag("+");
    diag("\n");
#endif

#else /*NO SIMPLIFY*/
    diag("simplification    : disabled\n");
    diag("SAT (full)        : ");
    mpz_out_str(stdout, 10, stats->tot_solutions);
    if (interrupted)
        diag("+");
    diag("\n");
#endif

#else // if GMP not defined 
    diag("gmp               : disabled\n");
#ifdef SIMPLIFY
    diag("simplification    : enabled\n");
    diag("SAT (partial)     : %12llu", stats->par_solutions);// partial assignments which cover the whole solution space.
    if (stats->par_solutions == ULONG_MAX || interrupted)
        diag("+");    // overflow or interrupted
    diag("\n");

#ifndef NONDISJOINT
    diag("SAT (full)        : %12llu", stats->tot_solutions); 
    if (stats->tot_solutions == ULONG_MAX || interrupted)
        diag("+");    // overflow or interrupted
    diag("\n");
#endif

#else /*NO SIMPLIFY*/
    diag("simplification    : disabled\n");
    diag("SAT (full)        : %12llu", stats->tot_solutions); 
    if (stats->tot_solutions == ULONG_MAX || interrupted)
        diag("+");    // overflow or interrupted
    diag("\n");
#endif
#endif // GMP
}

volatile sig_atomic_t eflag = 0;
static void SIGINT_handler(int signum)
{
	eflag = 1;
}


//=================================================================================================



static inline void PRINT_USAGE(char *p)
{
    printf("Usage:\t%s [options] input-file [output-file]\n", (p));
}


int main(int argc, char** argv)
{
    solver* s = solver_new();
    lbool   st;
    FILE *  in;
    FILE *  out;
    s->stats.clk = clock();

    char *infile  = NULL;
    char *outfile = NULL;
    int  lim, span;

    /*** RECEIVE INPUTS ***/
    for(int i = 1; i < argc; i++) {
      if(argv[i][0] == '-') {
        switch (argv[i][1]){
        case '\0': /* singular "-" */
          if (infile == NULL)       { infile  = ""; }
          else if (outfile == NULL) { outfile = ""; }
          break;
        case '?': case 'h': default:
          PRINT_USAGE(argv[0]); return  0;
        }
      } else {
        if(infile == NULL)        {infile  = argv[i];}
        else if(outfile == NULL)  {outfile = argv[i];}
        else                      {PRINT_USAGE(argv[0]); return  0;}
      }
    }
    infile  =  infile ?  infile : "";
    outfile = outfile ? outfile : "";

    /* Defaults (or "-") mean stdin and stdout */
    if (!*infile) { in = stdin; }
    else          { in = fopen(infile, "rb"); }
    if (in == NULL)
        warn("ERROR! Could not open file: %s\n", infile),
        exit(1);
    if (!*outfile) { out = stdout; }
    else           { out = fopen(outfile, "wb"); }
    if (out == NULL) {
        warn("ERROR! Could not open file: %s\n", outfile);
        exit(1);
    }
    s->out = out;

    st = parse_DIMACS(in, s);
    fclose(in);

    if (st == l_False){
        solver_delete(s);
        diag("Trivial problem\nUNSATISFIABLE\n");
        exit(20);
    }
    s->verbosity = 1;
    if (signal(SIGINT, SIGINT_handler) == SIG_ERR) {
        warn("ERROR! Cound not set signal");
        exit(1);
    }

    st = solver_solve(s,0,0);

    diag("input             : %s\n", infile);
	if (eflag == 1) {
    	diag("\n"); diag("*** INTERRUPTED ***\n");
    	printStats(&s->stats, clock() - s->stats.clk, true);
    	diag("\n"); diag("*** INTERRUPTED ***\n");
	} else {
    	printStats(&s->stats, clock() - s->stats.clk, false);
	}

    solver_delete(s);
    return 0;
}
