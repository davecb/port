#
# make port -- compile the pipeline component
#
BINARIES=port portsql
CFLAGS=-g -Wall -Werror # -Wextra
LINTFLAGS=-s -errtags #-erroff=E_GLOBAL_COULD_BE_STATIC2
SPLINTFLAGS=+posixlib -nullret -nullassign -mustfreeonly -mustfreefresh \
	-onlytrans -statictrans -temptrans -infloops -branchstate \
	-compdef -exitarg # Mildly usefull, not as good as lint/flint.
# Linux
LINT=splint ${SPLINTFLAGS}
# Solaris
# LINT=lint ${LINTFLAGS}

# all: install
all: install portsqltest


portsql: portsql.c
	#${LINT} portsql.c
	cc ${CFLAGS} -o portsql portsql.c ${HOME}/projects/Porting/blunder/strlcpy.c

port: port.c
	# ${LINT} port.c 
	cc ${CFLAGS} -o port port.c ${HOME}/projects/Porting/blunder/strlcpy.c

portsqltest: # Needs to be expanded.
	portsql -v portsql_tests/sql.cpp 2>&1 | more


porttest: port install
	for i in port_tests/*; do \
		echo $$i; \
		./port -I. -d dummy $$i; \
	done
	port -v -I. -d dummy tests/sql.c
	for i in tests/rev/*; do \
		echo $$i; \
		./port -I. -d aix2solaris $$i; \
		./port -r -d aix2solaris $$i; \
	done

# Linux and Solaris install code
install: port portsql
	-mkdir -p /opt/port/bin /opt/port/databases \
		/opt/port/src /opt/port/man/man1 \
		/opt/port/man/man4 /opt/port/src \
		/opt/port/src/tests
	-chmod -R +rw /opt/port
	-cp *.ref *.sqlref ../Databases
	-cp ../Databases/*ref /opt/port/databases
	-cp port port2* portsql /opt/port/bin
	-cp port*.1  /opt/port/man/man1
	-cp port.4 /opt/port/man/man4

# Older Solaris .pkg code
package: port
	rm -rf port
	mkdir -p port/opt/port/bin port/opt/port/databases \
		port/opt/port/src port/opt/port/man/man1 \
		port/opt/port/man/man4 port/opt/port/src \
		port/opt/port/src/tests
	cp ../Databases/*.ref port/opt/port/databases
	cp ../Databases/*.m4 port/opt/port/databases
	@# cp Makefile port.* port2* port/opt/port/src
	# cp tests/* port/opt/port/src/tests
	cp port*.1 port/opt/port/man/man1
	cp port.4 port/opt/port/man/man4
	pkg -v 1.1 port


solaris: package
	suid -c 'pkgadd -d ./port-1.1.pkg port'
	#su root -c 'pkgadd -d ./port-1.1.pkg port'

clean:
	rm -rf *.o port portsql

