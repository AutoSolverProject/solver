CC=g++
CFLAGS = -g -std=c++17


all: naive_lp_solver
	./naive_lp_solver

naive_lp_solver.o: naive_lp_solver.cpp
	$(CC) $(CFLAGS) -c naive_lp_solver.cpp

naive_lp_solver: naive_lp_solver.o
	$(CC) $(CFLAGS) naive_lp_solver.o -o naive_lp_solver

clean:
	$(RM) *.o naive_lp_solver *~ *core

depend:
	makedepend -- $(CFLAGS) -- $(SRC) $(LIBSRC)