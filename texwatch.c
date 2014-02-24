/*% cc -Wall -o # %
 * texmon texname [xpdfremote]
 *
 * Monitors tex files and compile
 * them on the fly.
 *
 * This program makes use of
 * the inotify(7) system to
 * watch tex files and rebuild
 * them when they change.
 */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/select.h>
#include <sys/wait.h>
#include <unistd.h>

#define MAX_PATH 1024

/* Define here the sequence of commands
 * to compile your tex files. The % will
 * be expanded with the tex file name with
 * the extension chopped.
 */
char *compile[] = {
	"pdflatex %",
#if 0
	"bibtex %",
	"pdflatex %",
	"pdflatex %",
#endif
	0
};

char *texname, texfile[MAX_PATH];
char *reloadcmd;
int errfd, notfd;

void
err(char *s)
{
	fprintf(stderr, "%s!\n", s);
}

int
runcmd(char *c)
{
	pid_t pid;
	char s[MAX_PATH], *p;
	char *args[4];
	int ret;

	args[0]="/bin/sh";
	args[1]="-c";
	args[3]=0;

	switch (pid=fork()) {
	case 0:
		p=strchr(c, '%');
		if (p)
			snprintf(s, MAX_PATH, "%.*s%s%s",
				(int)(p-c), c, texname, p+1);
		else
			snprintf(s, MAX_PATH, "%s", c);
		args[2]=s;
		close(0);
		dup2(errfd, 1);
		dup2(errfd, 2);
		execv(args[0], args);
		perror("execv");
		exit(1);
	default:
		while (wait(&ret)!=pid)
			continue;
		return WIFEXITED(ret)?WEXITSTATUS(ret):1;
	case -1:
		perror("fork");
		return -1;
	}
}

void
run(void)
{
	fd_set fs;
	int code;
	char **c;
	struct inotify_event ev;

	for (;;) {
		FD_ZERO(&fs);
		FD_SET(notfd, &fs);
		if (select(notfd+1, &fs, 0, 0, 0)==-1) {
			if (errno==EINTR || errno==EAGAIN)
				continue;
			perror("select");
			exit(1);
		}
		read(notfd, &ev, sizeof ev);
		if (ev.mask & IN_IGNORED
		&& inotify_add_watch(notfd, texfile, IN_MODIFY)==-1) {
			perror("inotify_add_watch");
			exit(1);
		}
		for (c=compile; *c; c++)
			if ((code=runcmd(*c))) {
				fprintf(stderr, "Command %s failed (%d)!\n",
					*c, code);
				break;
			}
		if (code==0 && runcmd(reloadcmd)) {
			err("Cannot sync xpdf, exiting");
			exit(1);
		}
	}
}

int
main(int argc, char *argv[])
{
	char *eod, *remote;

	if (argc<2) {
		fputs("usage: texwatch texname [xpdfremote]\n", stderr);
		exit(1);
	}
	texname=argv[1];
	eod=strrchr(texname, '/');
	if (eod) {
		*eod=0;
		if (chdir(texname)==-1) {
			perror("chdir");
			exit(1);
		}
		texname=eod+1;
	}
	snprintf(texfile, MAX_PATH, "%s.tex", texname);
	if (argc>2)
		remote=argv[2];
	else
		remote="viewer";

	errfd=2; /* We could log in a file. */
	reloadcmd=malloc(sizeof "xpdf -reload -remote "+strlen(remote));
	if (!reloadcmd) {
		err("Out of memory");
		exit(1);
	}
	sprintf(reloadcmd, "xpdf -reload -remote %s", remote);

	notfd=inotify_init();
	if (notfd==-1) {
		perror("inotify_init");
		exit(1);
	}
	if (inotify_add_watch(notfd, texfile, IN_MODIFY)==-1) {
		perror("inotify_add_watch");
		exit(1);
	}

	printf("Watching file %s\n", texfile);
	run();
	/* Silent GCC. */ exit(0);
}
