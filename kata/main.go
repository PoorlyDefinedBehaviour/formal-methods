package main

import (
	"encoding/json"
	"fmt"
	"iter"
	"os"
	"strconv"
)

type graph struct {
	Objects []object `json:"objects"`
	Edges   []edge   `json:"edges"`
}

type object struct {
	Gvid  int    `json:"_gvid"`
	Name  string `json:"name"`
	Label string `json:"label"`
	Shape string `json:"shape"`
	Style string `json:"style"`
}

type edge struct {
	Gvid      int    `json:"_gvid"`
	Tail      int    `json:"tail"`
	Head      int    `json:"head"`
	Color     string `json:"color"`
	FontColor string `json:"fontcolor"`
	Label     string `json:"label"`
}

type stateVisitor struct {
	graph *graph
	adj   map[int][]edge
}

func newStateVisitor(graph *graph) *stateVisitor {
	adj := make(map[int][]edge, 0)

	for _, edge := range graph.Edges {
		// If it is a stuttering step, skip it
		if edge.Tail == edge.Head {
			continue
		}

		adj[edge.Tail] = append(adj[edge.Tail], edge)
	}
	return &stateVisitor{graph: graph, adj: adj}
}

func initialState(objects []object) map[string]string {
	for _, object := range objects {
		if object.Shape == "box" {
			return parseLabel(object.Label)
		}
	}
	panic(fmt.Sprintf("unable to find initial state: objects=%+v", objects))
}

type Action struct {
	Name   string
	Values map[string]string
}

func (visitor *stateVisitor) Next() (iter.Seq[Action], bool) {
	initial := visitor.graph.Edges[0].Tail
	if len(visitor.adj[initial]) == 0 {
		return nil, false
	}

	return func(yield func(Action) bool) {
		initialState := initialState(visitor.graph.Objects)

		if !yield(Action{Name: "Init", Values: initialState}) {
			return
		}

		current := visitor.adj[initial][0]

		for {
			if !yield(Action{Name: current.Label}) {
				return
			}

			neighbors := visitor.adj[current.Head]
			if len(neighbors) == 0 {
				return
			}
			next := neighbors[0]

			updatedNeighbors := swapRemove(visitor.adj[current.Tail], 0)
			if len(updatedNeighbors) == 0 {
				delete(visitor.adj, current.Tail)
			} else {
				visitor.adj[current.Tail] = updatedNeighbors
			}

			current = next
		}
	}, true
}

func swapRemove(xs []edge, i int) []edge {
	xs[i] = xs[len(xs)-1]
	return xs[:len(xs)-1]
}

func main() {
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
}

type lexer struct {
	input    string
	position int
}

type tokenType int

const (
	tokenLeftBar tokenType = iota + 1
	tokenRightBar
	tokenEqual
	tokenIdentifier
	tokenNumber
)

func (t tokenType) String() string {
	switch t {
	case tokenLeftBar:
		return "\\"
	case tokenRightBar:
		return "/"
	case tokenEqual:
		return "="
	case tokenIdentifier:
		return "identifier"
	case tokenNumber:
		return "number"
	default:
		panic(fmt.Sprintf("unhandled token: %d", t))
	}
}

type token struct {
	typ   tokenType
	start int
	end   int
}

func (t token) String() string {
	return fmt.Sprintf("(%s, %d, %d)", t.typ, t.start, t.end)
}

func newLexer(input string) *lexer {
	return &lexer{input: input, position: 0}
}

func (l *lexer) nextCharacter() (byte, bool) {
	for {
		if l.position >= len(l.input) {
			return 0, false
		}

		c := l.input[l.position]
		l.position += 1

		// Skip whitespace
		if c == ' ' || c == '\n' || c == '\t' {
			continue
		}
		// Skip escape sequences
		if c == '\\' {
			next, _ := l.peek(0)
			if next == 'n' || c == 't' {
				_, _ = l.nextCharacter()
				continue
			}
		}
		return c, true
	}
}

func (l *lexer) peek(n int) (byte, bool) {
	if l.position+n >= len(l.input) {
		return 0, false
	}

	return l.input[l.position+n], true
}

func (l *lexer) identifier() token {
	start := l.position - 1

	for {
		c, ok := l.peek(0)
		if !ok || !isAsciiLetter(c) {
			break
		}
		_, _ = l.nextCharacter()
	}

	return token{typ: tokenIdentifier, start: start, end: l.position}
}

func (l *lexer) number() token {
	start := l.position - 1

	for {
		c, ok := l.peek(0)
		if !ok || !isNumber(c) {
			break
		}
		_, _ = l.nextCharacter()
	}

	return token{typ: tokenNumber, start: start, end: l.position}
}

func (l *lexer) nextToken() (token, bool) {
	c, ok := l.nextCharacter()
	if !ok {
		return token{}, ok
	}

	switch c {
	case '\\':
		return token{typ: tokenLeftBar, start: l.position, end: l.position + 1}, true
	case '/':
		return token{typ: tokenRightBar, start: l.position, end: l.position + 1}, true
	case '=':
		return token{typ: tokenEqual, start: l.position, end: l.position + 1}, true
	default:
		if isAsciiLetter(c) {
			return l.identifier(), true
		}

		if isNumber((c)) {
			return l.number(), true
		}

		panic(fmt.Sprintf("unhandled char: %+v", string(c)))
	}
}

func parseLabel(s string) map[string]string {
	lexer := newLexer(s)

	out := make(map[string]string)

	for {
		token, ok := lexer.nextToken()
		if !ok {
			break
		}

		if token.typ == tokenIdentifier {
			equalToken, ok := lexer.nextToken()
			if !ok || equalToken.typ != tokenEqual {
				panic(fmt.Sprintf("unexpected token after identifier token: token=%+v ok=%+v", equalToken, ok))
			}

			for {
				valueToken, ok := lexer.nextToken()
				if !ok {
					panic("expcted value token after identifier token but got EOF")
				}
				if valueToken.typ != tokenNumber {
					continue
				}

				out[lexer.input[token.start:token.end]] = lexer.input[valueToken.start:valueToken.end]
				break
			}
		}

	}

	return out
}

func isAsciiLetter(s byte) bool {
	return (s >= 'a' && s <= 'z') || (s >= 'A' && s <= 'Z')
}

func isNumber(s byte) bool {
	_, err := strconv.ParseInt(string(s), 10, 64)
	if err == nil {
		return true
	}

	_, err = strconv.ParseFloat(string(s), 64)
	return err == nil
}
