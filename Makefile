INC=/data/local/include
LIB=/data/local/lib

CC?=gcc
g: g.c
	$(CC) -O  -o g g.c -lm -lpthread -lflint -lmpfr -lgmp -larb
	#gcc -O -I$(INC) -I$(INC)/flint -o g g.c $(LIB)/libarb.a $(LIB)/libflint.a $(LIB)/libmpfr.a $(LIB)/libgmp.a -lm -lpthread
