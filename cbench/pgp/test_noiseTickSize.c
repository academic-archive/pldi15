// #define DELTAS 15		/* Number of deltas to try */
int DELTAS;

void gettimeofday(struct timeval { int tv_usec, tv_sec; } *tv, void *p)
{
	// do something simple
	return;
}

static unsigned noiseTickSize (void)
{
    int i;
    int j;
    unsigned t;
    unsigned *deltas/*[DELTAS]*/;
    struct timeval { int tv_usec, tv_sec; } tv_base, tv_old, tv_new;

    i = j = 0;
    gettimeofday(&tv_base, 0);
    tv_old = tv_base;
    do {
	gettimeofday(&tv_new, 0);

        assert(i < DELTAS); // help by giving the loop invariant

	if (tv_new.tv_usec > tv_old.tv_usec + 2) {
	    deltas[i++] = tv_new.tv_usec - tv_base.tv_usec +
		1000000 * (tv_new.tv_sec - tv_base.tv_sec);
	    tv_base = tv_new;
	    j = 0;
	}
	tv_old = tv_new;

	/*
	 * If we are forever getting <= 2 us, then just assume
	 * it's 2 us.
	 */
	assert(j < 10001);
	if (j++ >= 10000)
	    return 2;
    } while (i < DELTAS);

    // non-linear sort not done
    // qsort(deltas, DELTAS, sizeof(deltas[0]), noiseCompare);

    t = deltas[DELTAS / 2];	/* Median */

/* #ifdef NOISEDEBUG
    if (verbose)
	fprintf(pgpout, "t = %u, clock frequency is %u Hz\n",
		t, (2000000 + t) / (2 * t));
#endif */

    return t;
}

void start(void) { noiseTickSize(); }
