package main

import "fmt"

type T struct {
	x, y int
}

func main() {
	t := new(T)
	t.x = 1
	p := &t.x
	fmt.Print(*p)
}
