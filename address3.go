package main

type T struct {
	x, y int
}

func main() {
	t := new(T)
	t.x = 1
	fmt.print(t.x)
}
