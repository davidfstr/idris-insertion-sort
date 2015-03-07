compile:
	idris -o InsertionSort InsertionSort.idr

run: compile
	./InsertionSort
