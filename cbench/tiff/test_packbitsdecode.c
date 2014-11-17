void memcpy(void *dst, void *src, int n) {
        char *d = dst, *s = src;
        while (n > 0) {
                // *d = *s; // unsupported heap assignment
                d = d+1;
                s = s+1;
                n = n-1;
        }
}

typedef int tsize_t;
typedef int *tsample_t;
typedef char *tidata_t;

static int
PackBitsDecode(/* TIFF* tif, */ tidata_t op, tsize_t occ, tsample_t s, tsize_t cc)
{
        char *bp;
        int n;
        int b = -140;

        // bp = (char*) tif->tif_rawcp;
        // cc = tif->tif_rawcc;
        while (cc > 0 && occ > 0) {
                n = (long) *bp++, cc--;
                /*
                 * Watch out for compilers that
                 * don't sign extend chars...
                 */
                if (n >= 128)
                        n -= 256;
		assert(n<128); assert(n>-129);
                if (n < 0) {            /* replicate next byte -n+1 times */
                        if (n == -128)  /* nop */
                                /* continue */;
			else {
                                n = -n + 1;
                                occ -= n;
                                b = *bp++, cc--;
                                while (n-- > 0)
                                        *op++ = b;
			}
                } else {                /* copy next n+1 bytes literally */
                        memcpy(op, bp, ++n);
                        op += n; occ -= n;
                        bp += n; cc -= n;
                }
        }
        // tif->tif_rawcp = (tidata_t) bp;
        // tif->tif_rawcc = cc;
        if (occ > 0) {
        //        TIFFError(tif->tif_name,
        //            "PackBitsDecode: Not enough data for scanline %ld",
        //            (long) tif->tif_row);
                return (0);
        }
        /* check for buffer overruns? */
        return (1);
}

void start() { tidata_t op; tsize_t occ; tsample_t s; tsize_t cc; PackBitsDecode(op, occ, s, cc); }
