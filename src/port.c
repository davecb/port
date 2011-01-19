/*
 * port -- test an application for portability, using text databases 
 *
 * Copyright (C) 2006, David Collier-Brown, davecb@spamcop.net
 *
 * This program is free software: It is available under the terms
 * of the LGPL, Versions 2 or later, or of the (ex-Sun) CDDL.
 */
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>   /* For stat(). */
#include <limits.h>     /* for PATH_MAX */
#include <strings.h>    /* For strspn(). */
#include <string.h>
#include <ctype.h>      /* For isalnum(). */
#include <stdlib.h>     /* For calloc(). */
#include <assert.h>     /* For assert(). */
#include <fcntl.h>      /* For stat(). */
#include <sys/types.h>
#include <sys/stat.h>

/* Parameters */
/* #define DEBUG 1   */

/* File Globals. */
#define MAXLINE 1024
#define YES 1
#define NO 0

static char *ProgName = "";
static char CppOpts[MAXLINE];
static FILE *OutFP;
static int ErrnoProcessing = NO;
static int ErrnoLevel = -1;

static int Verbose = 0;
static int IgnoreIndirect = NO; /* Initially YES. */
static int RealCount = NO;
static int NoCPP = NO;
static int Reverse = NO;

/* Avoid using Sun cpp unless everything is perfect:  */
/* it exists after N errors, missing all later issues. */
static char *Cpp = "gcc -E";
/* SUNCPP is "cc -E -xCC -erroff" */
/* GNUCPP  is "gcc -E" */

static char *Database = "linux"; /* Default. */
#define DBPATH "/opt/port/databases/%s.ref"

/* Issue Database */
typedef struct issue_t {
	char	*interface;	/* Interface name. */
	int	weight;		/* AKA score. */
	int	rweight;	/* For reverse translations. */
	int	errno;		/* Is errno use a prerequisite? */
	int	keyword;	/* Don't report just functions. */
				/* Other flags go here. */
	int	count;		/* How many of these have we seen? */
	char	*description;	/* Optional comment and example text */
	char	*transform;	/* Optional shell command. */
	char	*rtransform;	/* Reverse-translation shell command. */
} ISSUE;

static ISSUE *IssueDB = NULL;
static int IssueElements = 0;


static int port(const char *file, struct stat *statbuf);
static char *gettok(/*@null@*/ char *string, const char *sep, char *nextc);
static char *quotespan(char *p);
static int followingParen(char *p, char ch);
static int pragma(char *buffer, int *lineNo, char *file);
static int parse(char *buffer, int *lineNo, char *file);
static void loadDatabase(char *name);
static ISSUE *inDatabase(char *token);
static int compareDb(const void *p, const void *q);
static void report(char *p, ISSUE *q, char *file, int lineNo, int errnoLive);
static void transform(char *p, char *q, ISSUE *r);
static void reportScore(void);
static char *rest(char *p);
static char *end(char *p);
static char *quote(char *p);
static char *skipb(char *p);
static char *skipcolon(char *p);
extern char *strdup(const char *s); /* For splint. */
extern FILE *popen(const char *command, const char *type);
extern int pclose(FILE *stream);
extern size_t strlcat(char *dst, const char *src, size_t dstsize);
extern size_t strlcpy(char *dst, const char *src, size_t dstsize);


static void usage() {
	(void) fprintf(stderr, "You must specify at least one file.\n");
	(void) fprintf(stderr, "Usage: %s [-d database][-Iinclude][-Ddefine][-eEilnsv] file\n",
		ProgName);
}

/*
 * main -- process options and set up the environment before
 *	running port().
 */
 int
main(int argc, char *argv[]) {
	int	i,
		rc = 0;
	struct stat statbuf;

	ProgName = argv[0];
	CppOpts[0] = '\0';

	/* Process options */
	for (i=1; i < argc; i++) {
		if (argv[i][0] == '-') {
			switch (argv[i][1]) {
			case 'D': /* -Ddefine */
				(void) strlcat(CppOpts, argv[i], MAXLINE);
				(void) strlcat(CppOpts, " ", MAXLINE);
				break;			  
			case 'd':
			  	Database = argv[i+1];
				i++;
				break;
			case 'e': /* grep for errno, database lacks ERRNO tag */
				ErrnoProcessing = YES;
				break;
			case 'i': /* Report indirect calls. */
				IgnoreIndirect = NO;
				break;
			case 'I': /* -Idir */
				(void) strlcat(CppOpts, argv[i], MAXLINE);
				(void) strlcat(CppOpts, " ", MAXLINE);
				break;			  
			case 'n': /*  NoCPP. */
				NoCPP = YES;
				break;
			case 'r': /*  Reverse. */
				Reverse = YES;
				break;
			case 's':
				RealCount = YES;
				break;
			case 'v':
				Verbose = 1;
				break;
			default:
				(void) fprintf(stderr, "%s: Unrecognized "
					"option \"-%c\" ignored.\n",
					ProgName, argv[i][1]);
				break;
			}
		}
		else {
			/* A file, so we stop processing options */
			break;
		}
	}
	if (i >= argc) {
		/* Someone forgot to specify a file. */
		usage();
		exit(1);
	}

	/* Open the pipe to the output filter */
	if ((OutFP = popen("sort -u -k 4,4 -k 1,1 -k 3,3n", "w")) == NULL) {
		 (void) fprintf(stderr, "%s: can't open a pipe to sort, "
			"halting.\n", ProgName);
		 exit(3);
	}
	
	/* Open and load database next. */
	loadDatabase(Database);


	/* Iterate across named files. */
	for ( ; i < argc; i++) {
		if (stat(argv[i], &statbuf) < 0) {
			(void) fprintf(stderr, "%s: can't open %s, ignored.\n",
				       ProgName, argv[i]);
			continue;
		}
		if (Verbose == 1) {
			(void) fprintf(stderr, "%s: porting %s\n",
				ProgName, argv[i]);
		}
		rc += port(argv[i], &statbuf);
	}
	(void) pclose(OutFP);

	reportScore();
	exit(rc);
}

/*
 * port -- process a file
 */
 static int
port(const char *path, struct stat *statbuf) {
	FILE	*fp;
	char	buffer[MAXLINE * 2];
	int	lineNo = 0,
		rc = 0;
	char	file[PATH_MAX+1];

        if (NoCPP == YES) {
                /* Turn off CPP for raw sql and languages CPP will mess up. */
                Cpp = "";
                (void) snprintf(CppOpts, sizeof(CppOpts),
                "echo \"# 1 \\\"$file\\\"\" ; cat $file");
        }


	if ((statbuf->st_mode & S_IFDIR) == S_IFDIR) {
		/* Use find at the beginning of the pipeline. */
		/* Select ONLY c, h and cpp files. */
		(void) snprintf(buffer, sizeof(buffer),
			"find %s -type f -name '*\\.c' "
			"-o -name '*\\.h' -o -name '*\\.cpp' "
			"-o -name '*\\.hh' | "
			"egrep -v 'SCCS|RCS|\\.svn' | "
			"while read file; do %s %s; done",
			path, Cpp, CppOpts);

	}
	else {
		if (NoCPP == YES) {
			(void) snprintf(buffer, sizeof(buffer),
			"export file=%s; %s",path, CppOpts);
		}
		else {
			/* Just run the input file through cpp. */
			(void) snprintf(buffer, sizeof(buffer),
				"%s %s %s ",
				Cpp, CppOpts, path);
		}
	}

	if ((fp = popen(buffer, "r")) == NULL) {
		(void) fprintf(stderr,"%s: can't preprocess %s using the "
			"command %s, halting.\n", ProgName, path,
			buffer);
		return 1;
	}

	for (; fgets(buffer, (int) sizeof(buffer), fp) != NULL; lineNo++) {
		if (Verbose == 1) {
			(void) fputs(buffer, stderr);
		}
		
		if (*buffer == '\n') {
			/*EMPTY*/
			; /* Just increment the line counter. */
		}
		else if (*buffer == '#') {
			/* Handle a pragma or # line directive. */
			rc += pragma(buffer, &lineNo, &file[0]);
		}
		else {
			rc += parse(buffer, &lineNo, &file[0]);
		}
	}
	(void) pclose(fp);
	return rc;
}

/*
 * pragma -- parse pragmas and #line directives
 */
 static int
pragma(char *buffer, int *lineNo, char *file) {
	char	*p, nextc;

	if (buffer[1] == ' ') {
		/* It's a # line directive, */
		/* get the lineNo and filename. */
		*lineNo = atoi(gettok(buffer, "# \t\n", &nextc)) -1;
		
		if ((p = gettok(NULL, " \t\n",&nextc)) != NULL) {
			(void) strlcpy(file, p, PATH_MAX);
		}

	}
	/* Otherwise its a pragma or #ident and we ignore it. */
	return 0;
 }

/*
 * parse -- parse the contents of a regular line
 */
 static int
parse(char *buffer, int *lineNo, char *file) {
	int	curlyLevel = 0;
	char	*p, nextc = '\0';
	const char *skip = " \t\n~!@#$%^&*()-+=[]|;<>,./?";
		/* This used to contain :s */
	ISSUE	*q;

	for (p=gettok(buffer, skip, &nextc); p != NULL;
					p = gettok(NULL, skip, &nextc)) {
#ifdef DEBUG	  
		(void) fprintf(stderr, ">> \"%s\"\n", p);
#endif
		
		if (isalnum(*p) || *p == '_') {
			/* Alphanumeric token. */
			if ((q = inDatabase(p)) != NULL
			   && (q->keyword == YES 
                               || followingParen(p, nextc) != 0)) {

				report(p, q, file, *lineNo,
				       (int)(ErrnoLevel >= curlyLevel));
			}
			else if (strstr(p, "errno") != NULL) {
				/* errno is mentioned. */
				ErrnoLevel = curlyLevel;
			}
		}
		else if (*p == '"' || *p == '\'') {
			/* Quoted string or character. */
			/*EMPTY */
			;
		}
		else if (*p == '{') {
			curlyLevel++;
		}

		else if (*p == '}') {
			if (ErrnoLevel == curlyLevel) {
				/* We passed the closing curly of */
				/* its declaration, turn it off. */
				ErrnoLevel = -1;
			}
			curlyLevel--;
		}
		else {
			/* End of line (or false negative). */
			break;
		}
	}
	return 0;
 }

/*
 * report -- report matches, conditionally on direct calls,
 *	presence of errno, etc.
 */
 static void
report(char *p, ISSUE *q, char *file, int lineNo, int errnoLive) {
	char	*annotations = "";

	/* Never report if the source is in /user/include. */
	if (strncmp("/usr/include", &file[1], 10) == 0) {
		return;
	}

	/* Update count of interfaces to port. */
	q->count++;
		
	/* Ignore (annotate) likely false positives. */
	if (q->errno == 1 && errnoLive == 0) {
		/* If this test requires errno to be live and */
		/* it isn't, mark the line "NC". */
		annotations = "NC, errno not live";
		if (RealCount == YES) {
			q->count--;
		}		
	}
	else if (IgnoreIndirect == YES && strchr(">:.", *(p-1)) != NULL) {
	  	/* Ignore indirect and method calls: */
		/* this is probably not the library call we care about. */
		annotations  = "NC, not indirect";
		if (RealCount == YES) {
			q->count--;
		}

	}

	/* Report in error-message format. */
  	(void) fprintf(OutFP,"%s, line %d: %s %s ",
		file, lineNo, p, annotations);
#ifdef DEBUG
	(void) fprintf(stderr, "interface=%s, "
	     "weight=%d, rweight=%d errno=%d\n",
	      q->interface,
	      q->weight,
	      q->rweight,
	      q->errno);
	if (q->transform != NULL) {
		(void) fprintf(stderr, "interface=%s, "
		"transform=\"%s\"\n",
			q->interface, q->transform);
	}
	if (q->rtransform != NULL) {
		(void) fprintf(stderr, "interface=%s, "
		"rtransform=\"%s\"\n",
		q->interface, q->rtransform);
	}
#endif /* DEBUG */
	
	/* Add transformation iff provided. */
	if (Reverse == 0) {
		if (q->transform != NULL && q->transform[0] != '\0') {
			transform(p, q->transform, q);
		}
	}
	else {
		/* Look for a reverse tramsform. */
		if (q->rtransform != NULL && q->rtransform[0] != '\0') {
			transform(p, q->rtransform, q);
		}
	}
	(void) fputc('\n', OutFP);
	
	if (Verbose == 1) {
		(void) fprintf(stderr, "## %s, line %d: %s %s, "
			"weight=%d, errno=%d\n",
			file, lineNo, p, annotations, q->weight, q->errno);
	}
 }

/*
 * transform -- pass the token and rest of line through
 *	a shell command and append to fp.
 */
 static void
transform(char *p, char *q, ISSUE *r) {
	char	buffer[MAXLINE];
	FILE	*pfp;

#ifdef DEBUG
	(void) fprintf(stderr, "transformtion = '%s'\n",q);
#endif
	if (r->keyword != NO) {
		/* Construct the line for the script to edit. */
		(void) snprintf(buffer, sizeof(buffer),
			"echo '%s %s' | %s 2>&1", 
			p, quote(rest(p)), q);
	}
	else {
		/* Insert the '(' the parser removed. */
		(void) snprintf(buffer, sizeof(buffer),
			"echo '%s(%s' | %s 2>&1", 
			p, quote(rest(p)), q);
	}

	if ((pfp = popen(buffer, "r")) != NULL) {
		while (fgets(buffer, (int) sizeof(buffer), pfp) != NULL) {
			if ((p = strchr(buffer, '\n')) != NULL) {
				*p = '\0';
			}
			(void) fputs(buffer, OutFP);
#ifdef DEBUG
			(void) fprintf(stderr, "transformed buffer was "
				"\"%s\"\n", buffer);
#endif
		}
		(void) pclose(pfp);
	}
	return;
}


/*
 * rest -- return the rest of a tokenized string.
 */
 static char *
rest(char *p) {
	p = end(p);
	p++;
	return p;
}

/*
 * end -- return a pointer to the null at the end of a string.
 */
 static char *
end(char *p) {
	while (*p != '\0')
		p++;
       return p;
}

/*
 * quote -- return a string with any ' characters
 *	protected from sh and echo. Serially reusable only.
 */
 static char *
quote(char *p) {
	static char buffer[MAXLINE];
	char	*q = &buffer[0];

	p = skipb(p);
	while (*p != '\0') {
		switch(*p) {
		case '\'':
			*q++ = '\\';
			*q++ = '0';
			*q++ = '4';
			*q++ = '7';
			p++;
			break;
		default:
			*q++ = *p++;
			break;
		}
	}
	*q = '\0';
	return &buffer[0];
}

/*
 * skipb - skip blanks and tabs.
 */
 static char *
skipb(char *p) {
	while (isspace((int)*p))
		p++;
	return p;
}

/*
 * reportScore -- at the very end, print a table of instances*weights
 *	for estimating purposes.
 */
 void
reportScore(void) {
        int	i, calls = 0,
		subtotal = 0,
		total = 0,
		weight;
	ISSUE *p;

	(void) fprintf(stdout, "\n%20s %6s %6s\n",
		       "Interface Name", "Weight", "Calls");
	(void) fprintf(stdout, "%20s %6s %6s\n",
			"--------------","------","-----");
      	for (p=IssueDB, i=0; i < IssueElements; i++,p++) {
		if (p->count > 0) {
 			weight = (Reverse == 1)? p->rweight: p->weight;
			(void)fprintf(stdout,"%20s %6d %6d\n",
				      p->interface, weight, p->count);
			calls += p->count;
			subtotal += weight;
			total += (p->weight * p->count);
		}
	}
		(void) fprintf(stdout, "%20s %6s %6s\n",
			"--------------","------","-----");
		(void) fprintf(stdout, "%20s %6d %6d\n",
			"Total", subtotal, calls);
		(void) fprintf(stdout, "%20s %6d\n",
			"Difficulty", total);
 }

/*
 * loadDatabase -- load an issues file into an issue structure
 */
 static void
loadDatabase(char *name) {
	char	file[PATH_MAX],
		buffer[MAXLINE],
		nextc,
		*p;
	FILE	*fp;
	ISSUE	*issue;
	int	lines = 0;
	
	if ((p = strstr(name, ".ref")) != NULL) {
		*p = '\0'; /* Trim off .ref */
	}
	(void) snprintf(file, sizeof(file), DBPATH, name);
	if ((fp = fopen(file, "r")) == NULL) {
		(void) fprintf(stderr, "%s: can't load database \"%s\", "
			"halting.\n", ProgName, file);
		exit(3);
	}
	IssueDB = calloc(10240, sizeof(struct issue_t));
	assert(IssueDB != NULL);
	issue = IssueDB;

	for(; fgets(buffer, (int) sizeof(buffer), fp) != NULL; lines++) {
		assert(IssueElements < 10240);
		
		/* (void) fputs(buffer, stdout); */
		if (*buffer == '#') {
			/*EMPTY*/
			; /* Skip comments. */
		}
		else if (*buffer == '%') {
			/* Copy to stdout. */
			(void) printf("%s",buffer);
		}
		else if (strncmp(buffer, "NAME", 4) == 0) {
			  issue->interface = strdup(
				gettok(skipcolon(&buffer[4])," \t\n", &nextc));
		}
		else if (strncmp(buffer, "WEIGHT:", 7) == 0) {
			issue->weight = atoi(&buffer[7]);		  ;
		}
		else if (strncmp(buffer, "RWEIGHT:", 8) == 0) {
			issue->rweight = atoi(&buffer[8]);		  ;
		}
		else if (strncmp(buffer, "ERRNO", 5) == 0) {
			/* Non-probabalistic errno flag */
			issue->errno = YES;
		}
		else if (strncmp(buffer, "TRANSFORM:", 10) == 0) {
			/* Transform, as a shell script or exprssion. */
			issue->transform = strdup(&buffer[10]);
		}
		else if (strncmp(buffer, "RTRANSFORM:", 11) == 0) {
			/* Reverse transform, as a script or expression. */
			issue->rtransform = strdup(&buffer[11]);
		}
		else if (strncmp(buffer, "KEYWORD", 7) == 0) {
			/* match keywords, not just function calls. */
			issue->keyword = YES;
		}
		else if (strncmp(buffer, "BEGIN_COMMENT", 8) == 0
		     || strncmp(buffer, "END_COMMENT", 8) == 0
		     || strncmp(buffer, "BEGIN_EXAMPLE", 8) == 0) {
			/*EMPTY*/
			; /* We use these elsewhere. */
		}
		else if (strncmp(buffer, "END_EXAMPLE", 8) == 0) {
			if (issue->interface == NULL) {
				(void) fprintf(stderr,
					"%s: missing interface name "
					"in %s, line %d.\n",
					 ProgName, file, lines);
			}
			issue->count = 0;
#ifdef DEBUG
			(void) fprintf(stderr, "interface=%s, "
			     "weight=%d, rweight=%d errno=%d, issue=%d\n",
			      issue->interface,
			      issue->weight,
			      issue->rweight,
			      issue->errno,
			      IssueElements);
			if (issue->transform != NULL) {
				(void) fprintf(stderr, "interface=%s, "
				"transform=\"%s\"\n",
				issue->interface, issue->transform);
			}
			if (issue->rtransform != NULL) {
				(void) fprintf(stderr, "interface=%s, "
				"rtransform=\"%s\"\n",
				issue->interface, issue->rtransform);
			}
			
#endif /* DEBUG */
			issue++;
			IssueElements++;
		}
		else {
			/* Conditionally check to see if errno is mentioned. */
			/* Not needed if database has ERRNO tags in it. */
			if (ErrnoProcessing == YES &&
			    (strstr(buffer, "errno") != NULL
			     || strstr(buffer, "error condition") != NULL)) {
				issue->errno = 1;
			}
		}
	}
	(void) fclose(fp);
	(void) qsort(IssueDB, (size_t)IssueElements, sizeof(struct issue_t), compareDb);
 }


/*
 * compareDb -- sorting comparison function
 */
static int compareDb(const void *p, const void *q) {
	return strcmp(((ISSUE *)p)->interface,((ISSUE *)q)->interface);
}

#ifdef undef
/*
 * seachDb -- bsearch comparison function
 */
static int searchDb(const void *key, const void *issue) {
	return strcmp((char *)key,((ISSUE *)issue)->interface);
}
#endif


/*
 * inDatabase -- see if a token is an interface-name in the database.
 */
 static ISSUE *
inDatabase(char *key) {
	static ISSUE *p,
		dummy;
	dummy.interface = key;
	if ((p = (ISSUE *)bsearch(&dummy, IssueDB, (size_t)IssueElements,
			     sizeof(struct issue_t), compareDb)) == NULL) { 
	        return NULL;
	}
	else {
		/* Belt and suspenders, methinks. */
		return (strcmp(p->interface, key) == 0)? p: NULL;
	}
}
   

/*
 * skipcolon -- skip over colons
 */
 static char *
skipcolon(char *p) {
	while (*p == ':') {
		p++;
	}
	return p;
}


/*
 * gettok -- get a token from a line, much like strtok, except make
 *	the next character visible in a variable for lookahead and
 *	handle quoted strings.
 */
 static char *
gettok(char *string, const char *skip, char *nextc) {
	static char *p, *q;

	if (string != NULL ) {
		/* Initialize everything */
		p = q = string;
		*nextc = ' ';
	}
	else {
		/* put nextc back. */
		*q = *nextc;
		/* Set p to beginning of next token. Note that */
		/* this assumes nextc is NOT part of the token. */
		p = q + 1;  /* portsql is different here. */
	}

	if (*q == '\0' || *p == '\0') {
	  /* We hit the end of the line. */
		return NULL;
	}

	/* Skip over the uninteresting stuff */
        p += strspn(p, skip);

	/* If we found a string, take it as the token. */
	if (*p == '"' || *p == '\'') {
		q = quotespan(p);
	}
	else {
		q = p + strcspn(p, skip);
	}
	*nextc = *q;
	*q = '\0';
	return p;
 }

/*
.* quotespan -- advance pointer over a string, ignoring
 *	any escaped characters. Return a pointer, not a length.
 */
 static char *
quotespan(char *p) {
	char	ch = *p;

	for (p++;  *p != '\0' && *p != ch; p++) {
		if (*p == '\\') {
			/* Skip this and next char */
			 p++;
		}
	}
	return ++p;
}

/*
 * followingParen -- see if the next non-whitespace is a '('.
 *	Used in concert with gettok().
 */
 static int
followingParen(char *p, char ch) {
	if (ch == '(') {
		return YES;
	}
	/* Skip to end of string, then over the null */
	while (*p != '\0')
		p++;
	p++;
	  
	/* Skip whitespace */
	for (; *p != '\0'; p++) {
		if ( !isspace(*p)) {
			break;
		}
	}
	return (int)(*p == '(');
 }
