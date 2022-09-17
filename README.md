HVM on JavaScript
=================

[HVM](https://github.com/kindelia/hvm) is now available as a JavaScript library!

Installing
----------

```bash
npm i --save hvm-js
```

Examples
--------

### Evaluating a term to normal form

```javascript
import hvm from "hvm-js";

// Instantiates an HVM runtime given a source code
var rt = await hvm(`
  (U60.sum 0) = 0
  (U60.sum n) = (+ n (U60.sum (- n 1)))
`);

console.log(rt.eval("(U60.sum 10000000)"));
```


### Evaluating to weak head normal form

```javascript
import hvm from "hvm-js";

// Instantiates an HVM runtime given a source code
var rt = await hvm.runtime(`
  (U60.sum 0) = 0
  (U60.sum n) = (+ n (U60.sum (- n 1)))
`);

// Allocates an expression without reducing it
let loc = rt.alloc_code("(U60.sum 10)");

// Reduces it to weak head normal form:
rt.reduce(loc);

// If the result is a number, print its value:
let term = rt.at(loc);
if (rt.get_tag(term) == rt.NUM) {
  console.log("Result is Num(" + rt.get_val(term) + ")");
}
```

### Running an IO program

```javascript
import hvm from "hvm-js";

var rt = await hvm(`
  Main =
    (IO.do_output "Name: " λ_
    (IO.do_input           λname
    (IO.do_output "Hi, "   λ_
    (IO.do_output name     λ_
    (IO.done 42)))))
`);

await rt.run_io_term({$: "Fun", name: "Main", args: []});
console.log("");
```
