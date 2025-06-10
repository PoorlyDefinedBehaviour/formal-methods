package main

import (
	"encoding/json"
	"fmt"
	"os"
	"testing"
)

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

	initialState := parseLabel(graph.Objects[4].Label)
	fmt.Printf("\n\naaaaaaa initialState %+v\n\n", initialState)

	visitor := newStateVisitor(&graph)

	for {
		iter, ok := visitor.Next()
		if !ok {
			break
		}

		for _, action := range iter {
			switch action {
			case "Init":
			case "IncrementX":
			case "IncrementY":
			default:
				panic(fmt.Sprintf("unhandled action: %+v", action))
			}
		}
	}
}
