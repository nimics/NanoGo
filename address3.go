package main

import "fmt"

type T struct {
	x, y int
}

func main() {
	t := new(T)
	t.x = 1
	fmt.Print(t.x)
}
