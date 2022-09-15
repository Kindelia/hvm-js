// FIXME: load hvm-nodejs on Node.js

export default function boot_hvm(init, hvm) {

  async function init_runtime(code) {
    await init();

    var rt = hvm.Runtime.from_code(code);

    var fns = Object.getOwnPropertyNames(hvm.Runtime).filter(fn => typeof hvm.Runtime[fn] === "function");
    for (var fn of fns) {
      rt[fn] = hvm.Runtime[fn];
    }

    rt.DP0 = hvm.Runtime.DP0();
    rt.DP1 = hvm.Runtime.DP1();
    rt.VAR = hvm.Runtime.VAR();
    rt.ARG = hvm.Runtime.ARG();
    rt.ERA = hvm.Runtime.ERA();
    rt.LAM = hvm.Runtime.LAM();
    rt.APP = hvm.Runtime.APP();
    rt.SUP = hvm.Runtime.SUP();
    rt.CTR = hvm.Runtime.CTR();
    rt.FUN = hvm.Runtime.FUN();
    rt.OP2 = hvm.Runtime.OP2();
    rt.NUM = hvm.Runtime.NUM();
    rt.ADD = hvm.Runtime.ADD();
    rt.SUB = hvm.Runtime.SUB();
    rt.MUL = hvm.Runtime.MUL();
    rt.DIV = hvm.Runtime.DIV();
    rt.MOD = hvm.Runtime.MOD();
    rt.AND = hvm.Runtime.AND();
    rt.OR  = hvm.Runtime.OR();
    rt.XOR = hvm.Runtime.XOR();
    rt.SHL = hvm.Runtime.SHL();
    rt.SHR = hvm.Runtime.SHR();
    rt.LTN = hvm.Runtime.LTN();
    rt.LTE = hvm.Runtime.LTE();
    rt.EQL = hvm.Runtime.EQL();
    rt.GTE = hvm.Runtime.GTE();
    rt.GTN = hvm.Runtime.GTN();
    rt.NEQ = hvm.Runtime.NEQ();

    rt.IO_DO_OUTPUT = rt.get_id("IO.do_output");
    rt.IO_DO_INPUT = rt.get_id("IO.do_input");
    rt.IO_DO_FETCH = rt.get_id("IO.do_fetch");
    rt.IO_DONE = rt.get_id("IO.done");

    rt.readback = loc => readback(rt, loc);
    rt.alloc_term = value => alloc_term(rt, value);
    rt.build_term = value => build_term(rt, value);
    rt.normalize_term = value => normalize_term(rt, value);
    rt.eval_term = value => eval_term(rt, value);

    rt.alloc_ptr = term => alloc_ptr(rt, term);
    rt.create_app = (func, argm) => create_app(rt, func, argm);
    rt.alloc_app = (func, argm) => alloc_app(rt, func, argm);
    rt.alloc_fun = (fun, args) => alloc_fun(rt, fun, args);
    rt.create_fun = (fun, args) => create_fun(rt, fun, args);
    rt.run_io = (host) => run_io(rt, host);
    rt.run_io_term = (host) => run_io_term(rt, host);

    rt.unstring = str => unstring(str);
    rt.string = term => string(term);
    rt.list = term => list(term);

    return rt;
  }

  // Reads an HVM term as a JSON
  // readback (rt: Runtime) (loc: u64) : JSON
  function readback(rt, loc, stks = {}) {
    var term = rt.at(loc);
    switch (hvm.Runtime.get_tag(term)) {
      case rt.VAR: {
        return {$: "Var", name: "x" + hvm.Runtime.get_loc(term)};
      }
      case rt.DP0: {
        var col = hvm.Runtime.get_ext(term);
        var val = rt.at(hvm.Runtime.get_loc(term, 2n));
        stks[col] = stks[col] || [];
        stks[col].push(false);
        var result = readback(rt, val, stks);
        stks[col].pop();
        return result;
      }
      case rt.DP1: {
        var col = hvm.Runtime.get_ext(term);
        var val = rt.at(hvm.Runtime.get_loc(term, 2n));
        stks[col] = stks[col] || [];
        stks[col].push(true);
        var result = readback(rt, val, stks);
        stks[col].pop();
        return result;
      }
      case rt.CTR: {
        var ctid = hvm.Runtime.get_ext(term);
        var name = rt.get_name(ctid);
        var arit = rt.get_arity(ctid);
        var args = [];
        for (var i = 0; i < arit; ++i) {
          var arg = hvm.Runtime.get_loc(term, BigInt(i));
          args.push(readback(rt, arg, stks));
        }
        return {$: "Ctr", name, args};
      }
      case rt.FUN: {
        var ctid = hvm.Runtime.get_ext(term);
        var name = rt.get_name(ctid);
        var arit = rt.get_arity(ctid);
        var args = [];
        for (var i = 0; i < arit; ++i) {
          var arg = hvm.Runtime.get_loc(term, BigInt(i));
          args.push(readback(rt, arg, stks));
        }
        return {$: "Fun", name, args};
      }
      case rt.LAM: {
        var name = "x" + loc;
        var body = hvm.Runtime.get_loc(term, 1n);
        var body = readback(rt, body, stks);
        return {$: "Lam", name, body};
      }
      case rt.APP: {
        var func = rt.at(hvm.Runtime.get_loc(term, 0n));
        var argm = rt.at(hvm.Runtime.get_loc(term, 1n));
        var func = readback(rt, func, stks);
        var argm = readback(rt, argm, stks);
        return {$: "App", func, argm};
      }
      case rt.SUP: {
        var col = hvm.Runtime.get_ext(term);
        var stack = stks[col] || [];
        if (stack.length > 0) {
          var val = rt.at(hvm.Runtime.get_loc(term, stack[stack.length - 1]));
          var old = stks.pop(col);
          var got = readback(rt, val, stks);
          stks[col].push(old);
          return got;
        } else {
          var name = "HVM.sup".to_string(); // lang::Term doesn't have a Sup variant
          var val0 = rt.at(hvm.Runtime.get_loc(term, 0n));
          var val1 = rt.at(hvm.Runtime.get_loc(term, 1n));
          var val0 = readback(rt, val0, stks);
          var val1 = readback(rt, val1, stks);
          return {$: "Sup", val0, val1};
        }
      }
      case rt.OP2: {
        var val0 = rt.at(hvm.Runtime.get_loc(term, 0n));
        var val1 = rt.at(hvm.Runtime.get_loc(term, 1n));
        var val0 = readback(rt, val0, stks);
        var val1 = readback(rt, val1, stks);
        var oper;
        switch (hvm.Runtime.get_ext(term)) {
          case rt.ADD: oper = "ADD"; break;
          case rt.SUB: oper = "SUB"; break;
          case rt.MUL: oper = "MUL"; break;
          case rt.DIV: oper = "DIV"; break;
          case rt.MOD: oper = "MOD"; break;
          case rt.AND: oper = "AND"; break;
          case rt.OR : oper = "OR"; break;
          case rt.XOR: oper = "XOR"; break;
          case rt.SHL: oper = "SHL"; break;
          case rt.SHR: oper = "SHR"; break;
          case rt.LTN: oper = "LTN"; break;
          case rt.LTE: oper = "LTE"; break;
          case rt.EQL: oper = "EQL"; break;
          case rt.GTE: oper = "GTE"; break;
          case rt.GTN: oper = "GTN"; break;
          case rt.NEQ: oper = "NEQ"; break;
          default: oper = "?"; break;
        };
        return oper;
      }
      case rt.NUM: {
        var numb = hvm.Runtime.get_val(term);
        return {$: "Num", numb};
      }
      default: {
        return null;
      }
    }
  }

  // Builds a JS value on HVM. Returns the pointer.
  function build_term(rt, value) {
    switch (value.$) {
      case "Num": {
        return rt.Num(value.numb);
      }
      case "Ctr": case "Fun": {
        var ctid = rt.get_id(value.name);
        var arit = rt.get_arity(ctid); // todo: assert == length ?
        var host = rt.alloc(BigInt(value.args.length));
        for (var i = 0n; i < value.args.length; ++i) {
          rt.link(host + i, build_term(rt, value.args[i]));
        }
        var term = value.$ === "Ctr" ? rt.Ctr(ctid, host) : rt.Fun(ctid, host);
        return term;
      }
      case "App": {
        var host = rt.alloc(arit);
        rt.link(host + 0n, build_term(rt, value.func));
        rt.link(host + 1n, build_term(rt, value.argm));
        return rt.App(host);
      }
      default: {
        throw "JS conversion not supported yet for: " + JSON.stringify(value);
      }
    }
  }

  // Builds a JS value on HVM. Returns the location.
  function alloc_term(rt, value) {
    var loc = rt.alloc(1n);
    var ptr = build_term(rt, value);
    rt.link(loc, ptr);
    return loc;
  }

  // Builds a JS value on HVM. Normaliees. Returns the location.
  function normalize_term(rt, value) {
    var loc = alloc_term(rt, value);
    rt.normalize(loc);
    return loc;
  }

  // Builds a JS value on HVM. Normaliees. Returns the resulting term.
  function eval_term(rt, value) {
    return readback(rt, normalize_term(rt, value));
  }

  // unstring (str: String) : JSON
  function unstring(str) {
    var obj = {"$": "Ctr", name: "String.nil", args: []};
    for (var i = 0; i < str.length; ++i) {
      var num = {"$": "Num", numb: BigInt(str.charCodeAt(str.length - i - 1))};
      obj = {"$": "Ctr", name: "String.cons", args: [num, obj]};
    }
    return obj;
  }

  function alloc_ptr(rt, term) {
    var host = rt.alloc(1n);
    rt.link(host, term);
    return host;
  }

  function create_app(rt, func, argm) {
    var host = rt.alloc(2n);
    rt.link(host + 0n, func);
    rt.link(host + 1n, argm);
    return rt.App(host);
  }

  function create_fun(rt, fun, args) {
    let node = rt.alloc(BigInt(args.length));
    for (var i = 0; i < args.length; ++i) {
      rt.link(node + BigInt(i), args[i]);
    }
    return rt.Fun(fun, node);
  }

  function alloc_app(rt, func, argm) {
    var app = rt.create_app(func, argm);
    return alloc_ptr(rt, app);
  }

  function alloc_fun(rt, fun, args) {
    var fun = rt.create_fun(fun, args);
    return alloc_ptr(rt, fun);
  }

  // Runs an IO action. Returns the result Ptr. Clears host.
  async function run_io(rt, host) {
    rt.reduce(host);
    //console.log("run_io", rt.show(host));
    var term = rt.at(host);
    switch (rt.get_tag(term)) {
      case rt.CTR: {
        var ctid = rt.get_ext(term);
        switch (ctid) {
          case rt.IO_DO_OUTPUT: {
            rt.normalize(rt.get_loc(term, 0n))
            var text = rt.string(rt.readback(rt.get_loc(term, 0n)));
            var cont = rt.at(rt.get_loc(term, 1n));
            await rt.do_output(text);
            var cont = rt.alloc_app(cont, rt.Num(0n));
            var done = await run_io(rt, cont);
            rt.clear(host, 1n);
            rt.clear(rt.get_loc(term, 0n), 2n);
            var text = rt.at(rt.get_loc(term, 0n));
            rt.collect(text);
            return done;
          }
          case rt.IO_DO_INPUT: {
            var cont = rt.at(rt.get_loc(term, 0n)); 
            var text = await rt.do_input();
            var text = rt.at(rt.alloc_term(rt.unstring(text)));
            var cont = rt.alloc_app(cont, text);
            var done = await run_io(rt, cont);
            rt.clear(host, 1n);
            rt.clear(rt.get_loc(term, 0n), 1n);
            return done;
          }
          case rt.IO_DO_FETCH: {
            var url = rt.string(rt.readback(rt.get_loc(term, 0n)));
            var body = await (await fetch(url)).text();
            var text = rt.at(rt.alloc_term(rt.unstring(body)));
            var cont = rt.at(rt.get_loc(term, 2n)); 
            var cont = rt.alloc_app(cont, text);
            var done = await run_io(rt, cont);
            rt.clear(host, 1n);
            rt.clear(rt.get_loc(term, 0n), 3n);
            var url = rt.at(rt.get_loc(term, 0n));
            rt.collect(url);
            var opts = rt.at(rt.get_loc(term, 1n));
            rt.collect(opts);
            return done;
          }
          case rt.IO_DONE: {
            // TODO: implement compute_at
            rt.reduce(rt.get_loc(term, 0n));
            let retr = rt.at(rt.get_loc(term, 0n));
            rt.clear(host, 1n);
            rt.clear(rt.get_loc(term, 0n), 1n);
            return retr;
          }
          break;
        }
      }
      default: {
        throw "HVM effect runtime type error.";
      }
    }
  }

  function run_io_term(rt, value) {
    return run_io(rt, alloc_term(rt, value));
  }

  // string (term: JSON) : Option String
  function string(term) {
    var text = "";
    while (1) {
      if (term.$ === "Ctr") {
        if ( term.name === "String.cons"
          && term.args.length === 2
          && term.args[0].$ === "Num") {
          text = text + String.fromCharCode(Number(term.args[0].numb));
          term = term.args[1];
          continue;
        }
        if (term.name === "String.nil" && term.args.length === 0) {
          return text;
        }
      }
    }
    return null;
  }

  // list (term: JSON) : Option (List JSON)
  function list(term) {
    var list = [];
    while (1) {
      if (term.$ === "Ctr") {
        if (term.name === "List.cons" && term.args.length === 2) {
          list.push(term.args[0]);
          term = term.args[1];
          continue;
        }
        if (term.name === "List.nil" && term.args.length === 0) {
          return list;
        }
      }
    }
    return null;
  }

  return init_runtime;
};
