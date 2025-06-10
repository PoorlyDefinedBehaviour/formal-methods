package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"testing"

	"github.com/stretchr/testify/require"
)

type sut struct {
	x int
	y int
}

func TestStates(t *testing.T) {
	t.Parallel()

	file, err := os.Open("./out.json")
	if err != nil {
		panic(err)
	}

	var graph graph
	if err := json.NewDecoder(file).Decode(&graph); err != nil {
		panic(err)
	}

	visitor := newStateVisitor(&graph)

	for {
		fmt.Printf("\n\naaaaaaa ----\n\n")
		iter, ok := visitor.Next()
		if !ok {
			break
		}

		var sut sut

		for action := range iter {
			fmt.Printf("\n\naaaaaaa action %+v\n\n", action)
			switch action.Name {
			case "Init":
				x, err := strconv.ParseInt(action.Values["x"], 10, 64)
				require.NoError(t, err)
				y, err := strconv.ParseInt(action.Values["y"], 10, 64)
				require.NoError(t, err)
				sut.x = int(x)
				sut.y = int(y)
			case "IncrementX":
				sut.x += 1
			case "IncrementY":
				sut.y += 1
			default:
				panic(fmt.Sprintf("unhandled action: %+v", action))
			}
		}

		fmt.Printf("\n\naaaaaaa sut %+v\n\n", sut)
	}
}
