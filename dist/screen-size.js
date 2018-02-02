"use strict";
var __haste_prog_id = '649f1f018f69539146c0b6713e46067288ca544913672d681636a9f54a092a51';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=__Z,_1=function(_2,_){var _3=E(_2);if(!_3._){return _0;}else{var _4=B(_1(_3.b,_));return new T2(1,_3.a,_4);}},_5=function(_6){while(1){var _7=B((function(_8){var _9=E(_8);if(!_9._){return __Z;}else{var _a=_9.b,_b=E(_9.a);if(!_b._){_6=_a;return __continue;}else{return new T2(1,_b.a,new T(function(){return B(_5(_a));}));}}})(_6));if(_7!=__continue){return _7;}}},_c=new T(function(){return eval("(function(c){return document.getElementsByClassName(c);})");}),_d=function(_e,_f,_){var _g=B(A1(_e,_)),_h=B(A1(_f,_));return _g;},_i=function(_j,_k,_){var _l=B(A1(_j,_)),_m=B(A1(_k,_));return new T(function(){return B(A1(_l,_m));});},_n=function(_o,_p,_){var _q=B(A1(_p,_));return _o;},_r=function(_s,_t,_){var _u=B(A1(_t,_));return new T(function(){return B(A1(_s,_u));});},_v=new T2(0,_r,_n),_w=function(_x,_){return _x;},_y=function(_z,_A,_){var _B=B(A1(_z,_));return new F(function(){return A1(_A,_);});},_C=new T5(0,_v,_w,_i,_y,_d),_D=new T(function(){return B(unCStr("base"));}),_E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_F=new T(function(){return B(unCStr("IOException"));}),_G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_D,_E,_F),_H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_G,_0,_0),_I=function(_J){return E(_H);},_K=function(_L){return E(E(_L).a);},_M=function(_N,_O,_P){var _Q=B(A1(_N,_)),_R=B(A1(_O,_)),_S=hs_eqWord64(_Q.a,_R.a);if(!_S){return __Z;}else{var _T=hs_eqWord64(_Q.b,_R.b);return (!_T)?__Z:new T1(1,_P);}},_U=function(_V){var _W=E(_V);return new F(function(){return _M(B(_K(_W.a)),_I,_W.b);});},_X=new T(function(){return B(unCStr(": "));}),_Y=new T(function(){return B(unCStr(")"));}),_Z=new T(function(){return B(unCStr(" ("));}),_10=function(_11,_12){var _13=E(_11);return (_13._==0)?E(_12):new T2(1,_13.a,new T(function(){return B(_10(_13.b,_12));}));},_14=new T(function(){return B(unCStr("interrupted"));}),_15=new T(function(){return B(unCStr("system error"));}),_16=new T(function(){return B(unCStr("unsatisified constraints"));}),_17=new T(function(){return B(unCStr("user error"));}),_18=new T(function(){return B(unCStr("permission denied"));}),_19=new T(function(){return B(unCStr("illegal operation"));}),_1a=new T(function(){return B(unCStr("end of file"));}),_1b=new T(function(){return B(unCStr("resource exhausted"));}),_1c=new T(function(){return B(unCStr("resource busy"));}),_1d=new T(function(){return B(unCStr("does not exist"));}),_1e=new T(function(){return B(unCStr("already exists"));}),_1f=new T(function(){return B(unCStr("resource vanished"));}),_1g=new T(function(){return B(unCStr("timeout"));}),_1h=new T(function(){return B(unCStr("unsupported operation"));}),_1i=new T(function(){return B(unCStr("hardware fault"));}),_1j=new T(function(){return B(unCStr("inappropriate type"));}),_1k=new T(function(){return B(unCStr("invalid argument"));}),_1l=new T(function(){return B(unCStr("failed"));}),_1m=new T(function(){return B(unCStr("protocol error"));}),_1n=function(_1o,_1p){switch(E(_1o)){case 0:return new F(function(){return _10(_1e,_1p);});break;case 1:return new F(function(){return _10(_1d,_1p);});break;case 2:return new F(function(){return _10(_1c,_1p);});break;case 3:return new F(function(){return _10(_1b,_1p);});break;case 4:return new F(function(){return _10(_1a,_1p);});break;case 5:return new F(function(){return _10(_19,_1p);});break;case 6:return new F(function(){return _10(_18,_1p);});break;case 7:return new F(function(){return _10(_17,_1p);});break;case 8:return new F(function(){return _10(_16,_1p);});break;case 9:return new F(function(){return _10(_15,_1p);});break;case 10:return new F(function(){return _10(_1m,_1p);});break;case 11:return new F(function(){return _10(_1l,_1p);});break;case 12:return new F(function(){return _10(_1k,_1p);});break;case 13:return new F(function(){return _10(_1j,_1p);});break;case 14:return new F(function(){return _10(_1i,_1p);});break;case 15:return new F(function(){return _10(_1h,_1p);});break;case 16:return new F(function(){return _10(_1g,_1p);});break;case 17:return new F(function(){return _10(_1f,_1p);});break;default:return new F(function(){return _10(_14,_1p);});}},_1q=new T(function(){return B(unCStr("}"));}),_1r=new T(function(){return B(unCStr("{handle: "));}),_1s=function(_1t,_1u,_1v,_1w,_1x,_1y){var _1z=new T(function(){var _1A=new T(function(){var _1B=new T(function(){var _1C=E(_1w);if(!_1C._){return E(_1y);}else{var _1D=new T(function(){return B(_10(_1C,new T(function(){return B(_10(_Y,_1y));},1)));},1);return B(_10(_Z,_1D));}},1);return B(_1n(_1u,_1B));}),_1E=E(_1v);if(!_1E._){return E(_1A);}else{return B(_10(_1E,new T(function(){return B(_10(_X,_1A));},1)));}}),_1F=E(_1x);if(!_1F._){var _1G=E(_1t);if(!_1G._){return E(_1z);}else{var _1H=E(_1G.a);if(!_1H._){var _1I=new T(function(){var _1J=new T(function(){return B(_10(_1q,new T(function(){return B(_10(_X,_1z));},1)));},1);return B(_10(_1H.a,_1J));},1);return new F(function(){return _10(_1r,_1I);});}else{var _1K=new T(function(){var _1L=new T(function(){return B(_10(_1q,new T(function(){return B(_10(_X,_1z));},1)));},1);return B(_10(_1H.a,_1L));},1);return new F(function(){return _10(_1r,_1K);});}}}else{return new F(function(){return _10(_1F.a,new T(function(){return B(_10(_X,_1z));},1));});}},_1M=function(_1N){var _1O=E(_1N);return new F(function(){return _1s(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_0);});},_1P=function(_1Q){return new T2(0,_1R,_1Q);},_1S=function(_1T,_1U,_1V){var _1W=E(_1U);return new F(function(){return _1s(_1W.a,_1W.b,_1W.c,_1W.d,_1W.f,_1V);});},_1X=function(_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1s(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=44,_22=93,_23=91,_24=function(_25,_26,_27){var _28=E(_26);if(!_28._){return new F(function(){return unAppCStr("[]",_27);});}else{var _29=new T(function(){var _2a=new T(function(){var _2b=function(_2c){var _2d=E(_2c);if(!_2d._){return E(new T2(1,_22,_27));}else{var _2e=new T(function(){return B(A2(_25,_2d.a,new T(function(){return B(_2b(_2d.b));})));});return new T2(1,_21,_2e);}};return B(_2b(_28.b));});return B(A2(_25,_28.a,_2a));});return new T2(1,_23,_29);}},_2f=function(_2g,_2h){return new F(function(){return _24(_1X,_2g,_2h);});},_2i=new T3(0,_1S,_1M,_2f),_1R=new T(function(){return new T5(0,_I,_2i,_1P,_U,_1M);}),_2j=new T(function(){return E(_1R);}),_2k=function(_2l){return E(E(_2l).c);},_2m=__Z,_2n=7,_2o=function(_2p){return new T6(0,_2m,_2n,_0,_2p,_2m,_2m);},_2q=function(_2r,_){var _2s=new T(function(){return B(A2(_2k,_2j,new T(function(){return B(A1(_2o,_2r));})));});return new F(function(){return die(_2s);});},_2t=function(_2u,_){return new F(function(){return _2q(_2u,_);});},_2v=function(_2w){return new F(function(){return A1(_2t,_2w);});},_2x=function(_2y,_2z,_){var _2A=B(A1(_2y,_));return new F(function(){return A2(_2z,_2A,_);});},_2B=new T5(0,_C,_2x,_y,_w,_2v),_2C=function(_2D){return E(_2D);},_2E=new T2(0,_2B,_2C),_2F=function(_2G,_){var _2H=__arr2lst(0,_2G);return new F(function(){return _1(_2H,_);});},_2I=new T(function(){return eval("(function(e,q){if(!e || typeof e.querySelectorAll !== \'function\') {throw \'querySelectorAll not supported by this element\';} else {return e.querySelectorAll(q);}})");}),_2J=function(_2K){return E(E(_2K).b);},_2L=function(_2M,_2N,_2O){var _2P=function(_){var _2Q=__app2(E(_2I),E(_2N),toJSStr(E(_2O)));return new F(function(){return _2F(_2Q,_);});};return new F(function(){return A2(_2J,_2M,_2P);});},_2R=new T(function(){return B(unCStr(".js-screen-unit"));}),_2S=new T(function(){return B(unCStr(".js-screen-preview"));}),_2T=new T(function(){return B(unCStr(".js-height"));}),_2U=new T(function(){return B(unCStr(".js-width"));}),_2V=new T(function(){return B(unCStr(".js-diagonal"));}),_2W=new T(function(){return B(unCStr(".js-ratio"));}),_2X=function(_2Y,_){var _2Z=B(A(_2L,[_2E,_2Y,_2W,_])),_30=B(A(_2L,[_2E,_2Y,_2V,_])),_31=B(A(_2L,[_2E,_2Y,_2U,_])),_32=B(A(_2L,[_2E,_2Y,_2T,_])),_33=B(A(_2L,[_2E,_2Y,_2S,_])),_34=B(A(_2L,[_2E,_2Y,_2R,_]));return new T(function(){var _35=E(_2Z);if(!_35._){return __Z;}else{var _36=E(_30);if(!_36._){return __Z;}else{var _37=E(_31);if(!_37._){return __Z;}else{var _38=E(_32);if(!_38._){return __Z;}else{var _39=E(_33);if(!_39._){return __Z;}else{var _3a=E(_34);if(!_3a._){return __Z;}else{return new T1(1,new T6(0,_35.a,_36.a,_37.a,_38.a,_39.a,_3a.a));}}}}}}});},_3b=function(_3c,_){var _3d=E(_3c);if(!_3d._){return _0;}else{var _3e=B(_2X(_3d.a,_)),_3f=B(_3b(_3d.b,_));return new T2(1,_3e,_3f);}},_3g=function(_){var _3h=__app1(E(_c),"js-screen-size"),_3i=__arr2lst(0,_3h),_3j=B(_1(_3i,_)),_3k=B(_3b(_3j,_));return new T(function(){return B(_5(_3k));});},_3l=0,_3m=function(_){return _3l;},_3n=function(_3o,_3p,_){return new F(function(){return _3m(_);});},_3q="load",_3r="input",_3s="scroll",_3t="submit",_3u="blur",_3v="focus",_3w="change",_3x="unload",_3y=function(_3z){switch(E(_3z)){case 0:return E(_3q);case 1:return E(_3x);case 2:return E(_3w);case 3:return E(_3v);case 4:return E(_3u);case 5:return E(_3t);case 6:return E(_3s);default:return E(_3r);}},_3A=new T2(0,_3y,_3n),_3B="metaKey",_3C="shiftKey",_3D="altKey",_3E="ctrlKey",_3F="keyCode",_3G=function(_3H,_){var _3I=__get(_3H,E(_3F)),_3J=__get(_3H,E(_3E)),_3K=__get(_3H,E(_3D)),_3L=__get(_3H,E(_3C)),_3M=__get(_3H,E(_3B));return new T(function(){var _3N=Number(_3I),_3O=jsTrunc(_3N);return new T5(0,_3O,E(_3J),E(_3K),E(_3L),E(_3M));});},_3P=function(_3Q,_3R,_){return new F(function(){return _3G(E(_3R),_);});},_3S="keydown",_3T="keyup",_3U="keypress",_3V=function(_3W){switch(E(_3W)){case 0:return E(_3U);case 1:return E(_3T);default:return E(_3S);}},_3X=new T2(0,_3V,_3P),_3Y=function(_3Z){return E(_3Z);},_40=new T2(0,_2E,_w),_41="value",_42=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_43=function(_44,_){var _45=__app2(E(_42),_44,E(_41));return new T(function(){var _46=String(_45);return fromJSStr(_46);});},_47=function(_48,_49,_){var _4a=__app2(E(_42),_49,E(_41));return new T(function(){var _4b=String(_4a),_4c=Number(_4b),_4d=isDoubleNaN(_4c);if(!E(_4d)){return _4c;}else{return E(_48);}});},_4e=0,_4f=function(_4g,_4h){while(1){var _4i=E(_4g);if(!_4i._){return (E(_4h)._==0)?true:false;}else{var _4j=E(_4h);if(!_4j._){return false;}else{if(E(_4i.a)!=E(_4j.a)){return false;}else{_4g=_4i.b;_4h=_4j.b;continue;}}}}},_4k=new T(function(){return B(unCStr("5-4"));}),_4l=new T(function(){return B(unCStr("4-3"));}),_4m=new T(function(){return B(unCStr("21-9"));}),_4n=new T(function(){return B(unCStr("16-9"));}),_4o=new T(function(){return B(unCStr("16-10"));}),_4p=function(_4q){return (!B(_4f(_4q,_4o)))?(!B(_4f(_4q,_4n)))?(!B(_4f(_4q,_4m)))?(!B(_4f(_4q,_4l)))?(!B(_4f(_4q,_4k)))?1:1.25:1.3333333333333333:2.3333333333333335:1.7777777777777777:1.6;},_4r=function(_4s){return new F(function(){return _4p(_4s);});},_4t=function(_4u,_4v,_4w,_4x,_){var _4y=B(_43(_4u,_)),_4z=B(_47(_4e,E(_4v),_)),_4A=B(_47(_4e,E(_4w),_)),_4B=B(_47(_4e,E(_4x),_));return new T4(0,new T(function(){return B(_4r(_4y));}),_4z,_4A,_4B);},_4C=function(_){return _3l;},_4D=function(_4E){var _4F=E(_4E);return new F(function(){return Math.log(_4F+(_4F+1)*Math.sqrt((_4F-1)/(_4F+1)));});},_4G=function(_4H){var _4I=E(_4H);return new F(function(){return Math.log(_4I+Math.sqrt(1+_4I*_4I));});},_4J=function(_4K){var _4L=E(_4K);return 0.5*Math.log((1+_4L)/(1-_4L));},_4M=function(_4N,_4O){return Math.log(E(_4O))/Math.log(E(_4N));},_4P=3.141592653589793,_4Q=new T1(0,1),_4R=function(_4S,_4T){var _4U=E(_4S);if(!_4U._){var _4V=_4U.a,_4W=E(_4T);if(!_4W._){var _4X=_4W.a;return (_4V!=_4X)?(_4V>_4X)?2:0:1;}else{var _4Y=I_compareInt(_4W.a,_4V);return (_4Y<=0)?(_4Y>=0)?1:2:0;}}else{var _4Z=_4U.a,_50=E(_4T);if(!_50._){var _51=I_compareInt(_4Z,_50.a);return (_51>=0)?(_51<=0)?1:2:0;}else{var _52=I_compare(_4Z,_50.a);return (_52>=0)?(_52<=0)?1:2:0;}}},_53=new T(function(){return B(unCStr("base"));}),_54=new T(function(){return B(unCStr("GHC.Exception"));}),_55=new T(function(){return B(unCStr("ArithException"));}),_56=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_53,_54,_55),_57=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_56,_0,_0),_58=function(_59){return E(_57);},_5a=function(_5b){var _5c=E(_5b);return new F(function(){return _M(B(_K(_5c.a)),_58,_5c.b);});},_5d=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5e=new T(function(){return B(unCStr("denormal"));}),_5f=new T(function(){return B(unCStr("divide by zero"));}),_5g=new T(function(){return B(unCStr("loss of precision"));}),_5h=new T(function(){return B(unCStr("arithmetic underflow"));}),_5i=new T(function(){return B(unCStr("arithmetic overflow"));}),_5j=function(_5k,_5l){switch(E(_5k)){case 0:return new F(function(){return _10(_5i,_5l);});break;case 1:return new F(function(){return _10(_5h,_5l);});break;case 2:return new F(function(){return _10(_5g,_5l);});break;case 3:return new F(function(){return _10(_5f,_5l);});break;case 4:return new F(function(){return _10(_5e,_5l);});break;default:return new F(function(){return _10(_5d,_5l);});}},_5m=function(_5n){return new F(function(){return _5j(_5n,_0);});},_5o=function(_5p,_5q,_5r){return new F(function(){return _5j(_5q,_5r);});},_5s=function(_5t,_5u){return new F(function(){return _24(_5j,_5t,_5u);});},_5v=new T3(0,_5o,_5m,_5s),_5w=new T(function(){return new T5(0,_58,_5v,_5x,_5a,_5m);}),_5x=function(_5y){return new T2(0,_5w,_5y);},_5z=3,_5A=new T(function(){return B(_5x(_5z));}),_5B=new T(function(){return die(_5A);}),_5C=function(_5D,_5E){var _5F=E(_5D);return (_5F._==0)?_5F.a*Math.pow(2,_5E):I_toNumber(_5F.a)*Math.pow(2,_5E);},_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=_5J.a,_5L=E(_5I);return (_5L._==0)?_5K==_5L.a:(I_compareInt(_5L.a,_5K)==0)?true:false;}else{var _5M=_5J.a,_5N=E(_5I);return (_5N._==0)?(I_compareInt(_5M,_5N.a)==0)?true:false:(I_compare(_5M,_5N.a)==0)?true:false;}},_5O=function(_5P){var _5Q=E(_5P);if(!_5Q._){return E(_5Q.a);}else{return new F(function(){return I_toInt(_5Q.a);});}},_5R=function(_5S,_5T){while(1){var _5U=E(_5S);if(!_5U._){var _5V=_5U.a,_5W=E(_5T);if(!_5W._){var _5X=_5W.a,_5Y=addC(_5V,_5X);if(!E(_5Y.b)){return new T1(0,_5Y.a);}else{_5S=new T1(1,I_fromInt(_5V));_5T=new T1(1,I_fromInt(_5X));continue;}}else{_5S=new T1(1,I_fromInt(_5V));_5T=_5W;continue;}}else{var _5Z=E(_5T);if(!_5Z._){_5S=_5U;_5T=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_add(_5U.a,_5Z.a));}}}},_60=function(_61,_62){while(1){var _63=E(_61);if(!_63._){var _64=E(_63.a);if(_64==( -2147483648)){_61=new T1(1,I_fromInt( -2147483648));continue;}else{var _65=E(_62);if(!_65._){var _66=_65.a;return new T2(0,new T1(0,quot(_64,_66)),new T1(0,_64%_66));}else{_61=new T1(1,I_fromInt(_64));_62=_65;continue;}}}else{var _67=E(_62);if(!_67._){_61=_63;_62=new T1(1,I_fromInt(_67.a));continue;}else{var _68=I_quotRem(_63.a,_67.a);return new T2(0,new T1(1,_68.a),new T1(1,_68.b));}}}},_69=new T1(0,0),_6a=function(_6b,_6c){while(1){var _6d=E(_6b);if(!_6d._){_6b=new T1(1,I_fromInt(_6d.a));continue;}else{return new T1(1,I_shiftLeft(_6d.a,_6c));}}},_6e=function(_6f,_6g,_6h){if(!B(_5G(_6h,_69))){var _6i=B(_60(_6g,_6h)),_6j=_6i.a;switch(B(_4R(B(_6a(_6i.b,1)),_6h))){case 0:return new F(function(){return _5C(_6j,_6f);});break;case 1:if(!(B(_5O(_6j))&1)){return new F(function(){return _5C(_6j,_6f);});}else{return new F(function(){return _5C(B(_5R(_6j,_4Q)),_6f);});}break;default:return new F(function(){return _5C(B(_5R(_6j,_4Q)),_6f);});}}else{return E(_5B);}},_6k=function(_6l,_6m){var _6n=E(_6l);if(!_6n._){var _6o=_6n.a,_6p=E(_6m);return (_6p._==0)?_6o>_6p.a:I_compareInt(_6p.a,_6o)<0;}else{var _6q=_6n.a,_6r=E(_6m);return (_6r._==0)?I_compareInt(_6q,_6r.a)>0:I_compare(_6q,_6r.a)>0;}},_6s=new T1(0,1),_6t=function(_6u,_6v){var _6w=E(_6u);if(!_6w._){var _6x=_6w.a,_6y=E(_6v);return (_6y._==0)?_6x<_6y.a:I_compareInt(_6y.a,_6x)>0;}else{var _6z=_6w.a,_6A=E(_6v);return (_6A._==0)?I_compareInt(_6z,_6A.a)<0:I_compare(_6z,_6A.a)<0;}},_6B=new T(function(){return B(unCStr("base"));}),_6C=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6D=new T(function(){return B(unCStr("PatternMatchFail"));}),_6E=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6B,_6C,_6D),_6F=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6E,_0,_0),_6G=function(_6H){return E(_6F);},_6I=function(_6J){var _6K=E(_6J);return new F(function(){return _M(B(_K(_6K.a)),_6G,_6K.b);});},_6L=function(_6M){return E(E(_6M).a);},_6N=function(_6O){return new T2(0,_6P,_6O);},_6Q=function(_6R,_6S){return new F(function(){return _10(E(_6R).a,_6S);});},_6T=function(_6U,_6V){return new F(function(){return _24(_6Q,_6U,_6V);});},_6W=function(_6X,_6Y,_6Z){return new F(function(){return _10(E(_6Y).a,_6Z);});},_70=new T3(0,_6W,_6L,_6T),_6P=new T(function(){return new T5(0,_6G,_70,_6N,_6I,_6L);}),_71=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_72=function(_73,_74){return new F(function(){return die(new T(function(){return B(A2(_2k,_74,_73));}));});},_75=function(_76,_5y){return new F(function(){return _72(_76,_5y);});},_77=function(_78,_79){var _7a=E(_79);if(!_7a._){return new T2(0,_0,_0);}else{var _7b=_7a.a;if(!B(A1(_78,_7b))){return new T2(0,_0,_7a);}else{var _7c=new T(function(){var _7d=B(_77(_78,_7a.b));return new T2(0,_7d.a,_7d.b);});return new T2(0,new T2(1,_7b,new T(function(){return E(E(_7c).a);})),new T(function(){return E(E(_7c).b);}));}}},_7e=32,_7f=new T(function(){return B(unCStr("\n"));}),_7g=function(_7h){return (E(_7h)==124)?false:true;},_7i=function(_7j,_7k){var _7l=B(_77(_7g,B(unCStr(_7j)))),_7m=_7l.a,_7n=function(_7o,_7p){var _7q=new T(function(){var _7r=new T(function(){return B(_10(_7k,new T(function(){return B(_10(_7p,_7f));},1)));});return B(unAppCStr(": ",_7r));},1);return new F(function(){return _10(_7o,_7q);});},_7s=E(_7l.b);if(!_7s._){return new F(function(){return _7n(_7m,_0);});}else{if(E(_7s.a)==124){return new F(function(){return _7n(_7m,new T2(1,_7e,_7s.b));});}else{return new F(function(){return _7n(_7m,_0);});}}},_7t=function(_7u){return new F(function(){return _75(new T1(0,new T(function(){return B(_7i(_7u,_71));})),_6P);});},_7v=function(_7w){var _7x=function(_7y,_7z){while(1){if(!B(_6t(_7y,_7w))){if(!B(_6k(_7y,_7w))){if(!B(_5G(_7y,_7w))){return new F(function(){return _7t("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_7z);}}else{return _7z-1|0;}}else{var _7A=B(_6a(_7y,1)),_7B=_7z+1|0;_7y=_7A;_7z=_7B;continue;}}};return new F(function(){return _7x(_6s,0);});},_7C=function(_7D){var _7E=E(_7D);if(!_7E._){var _7F=_7E.a>>>0;if(!_7F){return  -1;}else{var _7G=function(_7H,_7I){while(1){if(_7H>=_7F){if(_7H<=_7F){if(_7H!=_7F){return new F(function(){return _7t("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7I);}}else{return _7I-1|0;}}else{var _7J=imul(_7H,2)>>>0,_7K=_7I+1|0;_7H=_7J;_7I=_7K;continue;}}};return new F(function(){return _7G(1,0);});}}else{return new F(function(){return _7v(_7E);});}},_7L=function(_7M){var _7N=E(_7M);if(!_7N._){var _7O=_7N.a>>>0;if(!_7O){return new T2(0, -1,0);}else{var _7P=function(_7Q,_7R){while(1){if(_7Q>=_7O){if(_7Q<=_7O){if(_7Q!=_7O){return new F(function(){return _7t("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7R);}}else{return _7R-1|0;}}else{var _7S=imul(_7Q,2)>>>0,_7T=_7R+1|0;_7Q=_7S;_7R=_7T;continue;}}};return new T2(0,B(_7P(1,0)),(_7O&_7O-1>>>0)>>>0&4294967295);}}else{var _7U=_7N.a;return new T2(0,B(_7C(_7N)),I_compareInt(I_and(_7U,I_sub(_7U,I_fromInt(1))),0));}},_7V=function(_7W,_7X){var _7Y=E(_7W);if(!_7Y._){var _7Z=_7Y.a,_80=E(_7X);return (_80._==0)?_7Z<=_80.a:I_compareInt(_80.a,_7Z)>=0;}else{var _81=_7Y.a,_82=E(_7X);return (_82._==0)?I_compareInt(_81,_82.a)<=0:I_compare(_81,_82.a)<=0;}},_83=function(_84,_85){while(1){var _86=E(_84);if(!_86._){var _87=_86.a,_88=E(_85);if(!_88._){return new T1(0,(_87>>>0&_88.a>>>0)>>>0&4294967295);}else{_84=new T1(1,I_fromInt(_87));_85=_88;continue;}}else{var _89=E(_85);if(!_89._){_84=_86;_85=new T1(1,I_fromInt(_89.a));continue;}else{return new T1(1,I_and(_86.a,_89.a));}}}},_8a=function(_8b,_8c){while(1){var _8d=E(_8b);if(!_8d._){var _8e=_8d.a,_8f=E(_8c);if(!_8f._){var _8g=_8f.a,_8h=subC(_8e,_8g);if(!E(_8h.b)){return new T1(0,_8h.a);}else{_8b=new T1(1,I_fromInt(_8e));_8c=new T1(1,I_fromInt(_8g));continue;}}else{_8b=new T1(1,I_fromInt(_8e));_8c=_8f;continue;}}else{var _8i=E(_8c);if(!_8i._){_8b=_8d;_8c=new T1(1,I_fromInt(_8i.a));continue;}else{return new T1(1,I_sub(_8d.a,_8i.a));}}}},_8j=new T1(0,2),_8k=function(_8l,_8m){var _8n=E(_8l);if(!_8n._){var _8o=(_8n.a>>>0&(2<<_8m>>>0)-1>>>0)>>>0,_8p=1<<_8m>>>0;return (_8p<=_8o)?(_8p>=_8o)?1:2:0;}else{var _8q=B(_83(_8n,B(_8a(B(_6a(_8j,_8m)),_6s)))),_8r=B(_6a(_6s,_8m));return (!B(_6k(_8r,_8q)))?(!B(_6t(_8r,_8q)))?1:2:0;}},_8s=function(_8t,_8u){while(1){var _8v=E(_8t);if(!_8v._){_8t=new T1(1,I_fromInt(_8v.a));continue;}else{return new T1(1,I_shiftRight(_8v.a,_8u));}}},_8w=function(_8x,_8y,_8z,_8A){var _8B=B(_7L(_8A)),_8C=_8B.a;if(!E(_8B.b)){var _8D=B(_7C(_8z));if(_8D<((_8C+_8x|0)-1|0)){var _8E=_8C+(_8x-_8y|0)|0;if(_8E>0){if(_8E>_8D){if(_8E<=(_8D+1|0)){if(!E(B(_7L(_8z)).b)){return 0;}else{return new F(function(){return _5C(_4Q,_8x-_8y|0);});}}else{return 0;}}else{var _8F=B(_8s(_8z,_8E));switch(B(_8k(_8z,_8E-1|0))){case 0:return new F(function(){return _5C(_8F,_8x-_8y|0);});break;case 1:if(!(B(_5O(_8F))&1)){return new F(function(){return _5C(_8F,_8x-_8y|0);});}else{return new F(function(){return _5C(B(_5R(_8F,_4Q)),_8x-_8y|0);});}break;default:return new F(function(){return _5C(B(_5R(_8F,_4Q)),_8x-_8y|0);});}}}else{return new F(function(){return _5C(_8z,(_8x-_8y|0)-_8E|0);});}}else{if(_8D>=_8y){var _8G=B(_8s(_8z,(_8D+1|0)-_8y|0));switch(B(_8k(_8z,_8D-_8y|0))){case 0:return new F(function(){return _5C(_8G,((_8D-_8C|0)+1|0)-_8y|0);});break;case 2:return new F(function(){return _5C(B(_5R(_8G,_4Q)),((_8D-_8C|0)+1|0)-_8y|0);});break;default:if(!(B(_5O(_8G))&1)){return new F(function(){return _5C(_8G,((_8D-_8C|0)+1|0)-_8y|0);});}else{return new F(function(){return _5C(B(_5R(_8G,_4Q)),((_8D-_8C|0)+1|0)-_8y|0);});}}}else{return new F(function(){return _5C(_8z, -_8C);});}}}else{var _8H=B(_7C(_8z))-_8C|0,_8I=function(_8J){var _8K=function(_8L,_8M){if(!B(_7V(B(_6a(_8M,_8y)),_8L))){return new F(function(){return _6e(_8J-_8y|0,_8L,_8M);});}else{return new F(function(){return _6e((_8J-_8y|0)+1|0,_8L,B(_6a(_8M,1)));});}};if(_8J>=_8y){if(_8J!=_8y){return new F(function(){return _8K(_8z,new T(function(){return B(_6a(_8A,_8J-_8y|0));}));});}else{return new F(function(){return _8K(_8z,_8A);});}}else{return new F(function(){return _8K(new T(function(){return B(_6a(_8z,_8y-_8J|0));}),_8A);});}};if(_8x>_8H){return new F(function(){return _8I(_8x);});}else{return new F(function(){return _8I(_8H);});}}},_8N=new T1(0,2147483647),_8O=new T(function(){return B(_5R(_8N,_6s));}),_8P=function(_8Q){var _8R=E(_8Q);if(!_8R._){var _8S=E(_8R.a);return (_8S==( -2147483648))?E(_8O):new T1(0, -_8S);}else{return new T1(1,I_negate(_8R.a));}},_8T=new T(function(){return 0/0;}),_8U=new T(function(){return  -1/0;}),_8V=new T(function(){return 1/0;}),_8W=0,_8X=function(_8Y,_8Z){if(!B(_5G(_8Z,_69))){if(!B(_5G(_8Y,_69))){if(!B(_6t(_8Y,_69))){return new F(function(){return _8w( -1021,53,_8Y,_8Z);});}else{return  -B(_8w( -1021,53,B(_8P(_8Y)),_8Z));}}else{return E(_8W);}}else{return (!B(_5G(_8Y,_69)))?(!B(_6t(_8Y,_69)))?E(_8V):E(_8U):E(_8T);}},_90=function(_91){var _92=E(_91);return new F(function(){return _8X(_92.a,_92.b);});},_93=function(_94){return 1/E(_94);},_95=function(_96){var _97=E(_96);return (_97!=0)?(_97<=0)? -_97:E(_97):E(_8W);},_98=function(_99){var _9a=E(_99);if(!_9a._){return _9a.a;}else{return new F(function(){return I_toNumber(_9a.a);});}},_9b=function(_9c){return new F(function(){return _98(_9c);});},_9d=1,_9e= -1,_9f=function(_9g){var _9h=E(_9g);return (_9h<=0)?(_9h>=0)?E(_9h):E(_9e):E(_9d);},_9i=function(_9j,_9k){return E(_9j)-E(_9k);},_9l=function(_9m){return  -E(_9m);},_9n=function(_9o,_9p){return E(_9o)+E(_9p);},_9q=function(_9r,_9s){return E(_9r)*E(_9s);},_9t={_:0,a:_9n,b:_9i,c:_9q,d:_9l,e:_95,f:_9f,g:_9b},_9u=function(_9v,_9w){return E(_9v)/E(_9w);},_9x=new T4(0,_9t,_9u,_93,_90),_9y=function(_9z){return new F(function(){return Math.acos(E(_9z));});},_9A=function(_9B){return new F(function(){return Math.asin(E(_9B));});},_9C=function(_9D){return new F(function(){return Math.atan(E(_9D));});},_9E=function(_9F){return new F(function(){return Math.cos(E(_9F));});},_9G=function(_9H){return new F(function(){return cosh(E(_9H));});},_9I=function(_9J){return new F(function(){return Math.exp(E(_9J));});},_9K=function(_9L){return new F(function(){return Math.log(E(_9L));});},_9M=function(_9N,_9O){return new F(function(){return Math.pow(E(_9N),E(_9O));});},_9P=function(_9Q){return new F(function(){return Math.sin(E(_9Q));});},_9R=function(_9S){return new F(function(){return sinh(E(_9S));});},_9T=function(_9U){return new F(function(){return Math.sqrt(E(_9U));});},_9V=function(_9W){return new F(function(){return Math.tan(E(_9W));});},_9X=function(_9Y){return new F(function(){return tanh(E(_9Y));});},_9Z={_:0,a:_9x,b:_4P,c:_9I,d:_9K,e:_9T,f:_9M,g:_4M,h:_9P,i:_9E,j:_9V,k:_9A,l:_9y,m:_9C,n:_9R,o:_9G,p:_9X,q:_4G,r:_4D,s:_4J},_a0=function(_a1,_a2){if(_a2<=0){var _a3=function(_a4){var _a5=function(_a6){var _a7=function(_a8){var _a9=function(_aa){var _ab=isDoubleNegativeZero(_a2),_ac=_ab,_ad=function(_ae){var _af=E(_a1);return (_af!=0)?_a2+_af:(_a2>=0)?(E(_ac)==0)?(_a2!=0)?_a2+_af:E(_af):3.141592653589793:3.141592653589793;};if(!E(_ac)){return new F(function(){return _ad(_);});}else{var _ag=E(_a1),_ah=isDoubleNegativeZero(_ag);if(!E(_ah)){return new F(function(){return _ad(_);});}else{return  -B(_a0( -_ag,_a2));}}};if(_a2>=0){return new F(function(){return _a9(_);});}else{var _ai=E(_a1),_aj=isDoubleNegativeZero(_ai);if(!E(_aj)){return new F(function(){return _a9(_);});}else{return  -B(_a0( -_ai,_a2));}}};if(_a2>0){return new F(function(){return _a7(_);});}else{var _ak=E(_a1);if(_ak>=0){return new F(function(){return _a7(_);});}else{return  -B(_a0( -_ak,_a2));}}};if(_a2>=0){return new F(function(){return _a5(_);});}else{var _al=E(_a1);if(_al<=0){return new F(function(){return _a5(_);});}else{return 3.141592653589793+Math.atan(_al/_a2);}}};if(_a2!=0){return new F(function(){return _a3(_);});}else{if(E(_a1)<=0){return new F(function(){return _a3(_);});}else{return 1.5707963267948966;}}}else{return new F(function(){return Math.atan(E(_a1)/_a2);});}},_am=function(_an,_ao){return new F(function(){return _a0(_an,E(_ao));});},_ap=function(_aq){var _ar=I_decodeDouble(_aq);return new T2(0,new T1(1,_ar.b),_ar.a);},_as=function(_at){var _au=B(_ap(E(_at)));return new T2(0,_au.a,_au.b);},_av=function(_aw,_ax){return new F(function(){return _5C(_aw,E(_ax));});},_ay=function(_az){var _aA=B(_ap(_az));return (!B(_5G(_aA.a,_69)))?_aA.b+53|0:0;},_aB=function(_aC){return new F(function(){return _ay(E(_aC));});},_aD=53,_aE=function(_aF){return E(_aD);},_aG=new T1(0,2),_aH=function(_aI){return E(_aG);},_aJ=1024,_aK= -1021,_aL=new T2(0,_aK,_aJ),_aM=function(_aN){return E(_aL);},_aO=function(_aP){var _aQ=isDoubleDenormalized(E(_aP));return (E(_aQ)==0)?false:true;},_aR=function(_aS){return true;},_aT=function(_aU){var _aV=isDoubleInfinite(E(_aU));return (E(_aV)==0)?false:true;},_aW=function(_aX){var _aY=isDoubleNaN(E(_aX));return (E(_aY)==0)?false:true;},_aZ=function(_b0){var _b1=isDoubleNegativeZero(E(_b0));return (E(_b1)==0)?false:true;},_b2=function(_b3,_b4){var _b5=E(_b3);if(!_b5){return E(_b4);}else{if(_b4!=0){var _b6=isDoubleFinite(_b4);if(!E(_b6)){return E(_b4);}else{var _b7=B(_ap(_b4)),_b8=_b7.a,_b9=_b7.b;if(2257>_b5){if( -2257>_b5){return new F(function(){return _5C(_b8,_b9+( -2257)|0);});}else{return new F(function(){return _5C(_b8,_b9+_b5|0);});}}else{return new F(function(){return _5C(_b8,_b9+2257|0);});}}}else{return E(_b4);}}},_ba=function(_bb,_bc){return new F(function(){return _b2(E(_bb),E(_bc));});},_bd=function(_be){return new F(function(){return _5C(B(_ap(E(_be))).a, -53);});},_bf=function(_bg,_bh){return (E(_bg)!=E(_bh))?true:false;},_bi=function(_bj,_bk){return E(_bj)==E(_bk);},_bl=new T2(0,_bi,_bf),_bm=function(_bn,_bo){return E(_bn)<E(_bo);},_bp=function(_bq,_br){return E(_bq)<=E(_br);},_bs=function(_bt,_bu){return E(_bt)>E(_bu);},_bv=function(_bw,_bx){return E(_bw)>=E(_bx);},_by=function(_bz,_bA){var _bB=E(_bz),_bC=E(_bA);return (_bB>=_bC)?(_bB!=_bC)?2:1:0;},_bD=function(_bE,_bF){var _bG=E(_bE),_bH=E(_bF);return (_bG>_bH)?E(_bG):E(_bH);},_bI=function(_bJ,_bK){var _bL=E(_bJ),_bM=E(_bK);return (_bL>_bM)?E(_bM):E(_bL);},_bN={_:0,a:_bl,b:_by,c:_bm,d:_bp,e:_bs,f:_bv,g:_bD,h:_bI},_bO=function(_bP){return new T1(0,_bP);},_bQ=function(_bR){var _bS=hs_intToInt64(2147483647),_bT=hs_leInt64(_bR,_bS);if(!_bT){return new T1(1,I_fromInt64(_bR));}else{var _bU=hs_intToInt64( -2147483648),_bV=hs_geInt64(_bR,_bU);if(!_bV){return new T1(1,I_fromInt64(_bR));}else{var _bW=hs_int64ToInt(_bR);return new F(function(){return _bO(_bW);});}}},_bX=new T(function(){var _bY=newByteArr(256),_bZ=_bY,_=_bZ["v"]["i8"][0]=8,_c0=function(_c1,_c2,_c3,_){while(1){if(_c3>=256){if(_c1>=256){return E(_);}else{var _c4=imul(2,_c1)|0,_c5=_c2+1|0,_c6=_c1;_c1=_c4;_c2=_c5;_c3=_c6;continue;}}else{var _=_bZ["v"]["i8"][_c3]=_c2,_c6=_c3+_c1|0;_c3=_c6;continue;}}},_=B(_c0(2,0,1,_));return _bZ;}),_c7=function(_c8,_c9){var _ca=hs_int64ToInt(_c8),_cb=E(_bX),_cc=_cb["v"]["i8"][(255&_ca>>>0)>>>0&4294967295];if(_c9>_cc){if(_cc>=8){var _cd=hs_uncheckedIShiftRA64(_c8,8),_ce=function(_cf,_cg){while(1){var _ch=B((function(_ci,_cj){var _ck=hs_int64ToInt(_ci),_cl=_cb["v"]["i8"][(255&_ck>>>0)>>>0&4294967295];if(_cj>_cl){if(_cl>=8){var _cm=hs_uncheckedIShiftRA64(_ci,8),_cn=_cj-8|0;_cf=_cm;_cg=_cn;return __continue;}else{return new T2(0,new T(function(){var _co=hs_uncheckedIShiftRA64(_ci,_cl);return B(_bQ(_co));}),_cj-_cl|0);}}else{return new T2(0,new T(function(){var _cp=hs_uncheckedIShiftRA64(_ci,_cj);return B(_bQ(_cp));}),0);}})(_cf,_cg));if(_ch!=__continue){return _ch;}}};return new F(function(){return _ce(_cd,_c9-8|0);});}else{return new T2(0,new T(function(){var _cq=hs_uncheckedIShiftRA64(_c8,_cc);return B(_bQ(_cq));}),_c9-_cc|0);}}else{return new T2(0,new T(function(){var _cr=hs_uncheckedIShiftRA64(_c8,_c9);return B(_bQ(_cr));}),0);}},_cs=function(_ct){var _cu=hs_intToInt64(_ct);return E(_cu);},_cv=function(_cw){var _cx=E(_cw);if(!_cx._){return new F(function(){return _cs(_cx.a);});}else{return new F(function(){return I_toInt64(_cx.a);});}},_cy=function(_cz){return I_toInt(_cz)>>>0;},_cA=function(_cB){var _cC=E(_cB);if(!_cC._){return _cC.a>>>0;}else{return new F(function(){return _cy(_cC.a);});}},_cD=function(_cE){var _cF=B(_ap(_cE)),_cG=_cF.a,_cH=_cF.b;if(_cH<0){var _cI=function(_cJ){if(!_cJ){return new T2(0,E(_cG),B(_6a(_4Q, -_cH)));}else{var _cK=B(_c7(B(_cv(_cG)), -_cH));return new T2(0,E(_cK.a),B(_6a(_4Q,_cK.b)));}};if(!((B(_cA(_cG))&1)>>>0)){return new F(function(){return _cI(1);});}else{return new F(function(){return _cI(0);});}}else{return new T2(0,B(_6a(_cG,_cH)),_4Q);}},_cL=function(_cM){var _cN=B(_cD(E(_cM)));return new T2(0,E(_cN.a),E(_cN.b));},_cO=new T3(0,_9t,_bN,_cL),_cP=function(_cQ){return E(E(_cQ).a);},_cR=function(_cS){return E(E(_cS).a);},_cT=new T1(0,1),_cU=function(_cV,_cW){if(_cV<=_cW){var _cX=function(_cY){return new T2(1,_cY,new T(function(){if(_cY!=_cW){return B(_cX(_cY+1|0));}else{return __Z;}}));};return new F(function(){return _cX(_cV);});}else{return __Z;}},_cZ=function(_d0){return new F(function(){return _cU(E(_d0),2147483647);});},_d1=function(_d2,_d3,_d4){if(_d4<=_d3){var _d5=new T(function(){var _d6=_d3-_d2|0,_d7=function(_d8){return (_d8>=(_d4-_d6|0))?new T2(1,_d8,new T(function(){return B(_d7(_d8+_d6|0));})):new T2(1,_d8,_0);};return B(_d7(_d3));});return new T2(1,_d2,_d5);}else{return (_d4<=_d2)?new T2(1,_d2,_0):__Z;}},_d9=function(_da,_db,_dc){if(_dc>=_db){var _dd=new T(function(){var _de=_db-_da|0,_df=function(_dg){return (_dg<=(_dc-_de|0))?new T2(1,_dg,new T(function(){return B(_df(_dg+_de|0));})):new T2(1,_dg,_0);};return B(_df(_db));});return new T2(1,_da,_dd);}else{return (_dc>=_da)?new T2(1,_da,_0):__Z;}},_dh=function(_di,_dj){if(_dj<_di){return new F(function(){return _d1(_di,_dj, -2147483648);});}else{return new F(function(){return _d9(_di,_dj,2147483647);});}},_dk=function(_dl,_dm){return new F(function(){return _dh(E(_dl),E(_dm));});},_dn=function(_do,_dp,_dq){if(_dp<_do){return new F(function(){return _d1(_do,_dp,_dq);});}else{return new F(function(){return _d9(_do,_dp,_dq);});}},_dr=function(_ds,_dt,_du){return new F(function(){return _dn(E(_ds),E(_dt),E(_du));});},_dv=function(_dw,_dx){return new F(function(){return _cU(E(_dw),E(_dx));});},_dy=function(_dz){return E(_dz);},_dA=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_dB=new T(function(){return B(err(_dA));}),_dC=function(_dD){var _dE=E(_dD);return (_dE==( -2147483648))?E(_dB):_dE-1|0;},_dF=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_dG=new T(function(){return B(err(_dF));}),_dH=function(_dI){var _dJ=E(_dI);return (_dJ==2147483647)?E(_dG):_dJ+1|0;},_dK={_:0,a:_dH,b:_dC,c:_dy,d:_dy,e:_cZ,f:_dk,g:_dv,h:_dr},_dL=function(_dM,_dN){if(_dM<=0){if(_dM>=0){return new F(function(){return quot(_dM,_dN);});}else{if(_dN<=0){return new F(function(){return quot(_dM,_dN);});}else{return quot(_dM+1|0,_dN)-1|0;}}}else{if(_dN>=0){if(_dM>=0){return new F(function(){return quot(_dM,_dN);});}else{if(_dN<=0){return new F(function(){return quot(_dM,_dN);});}else{return quot(_dM+1|0,_dN)-1|0;}}}else{return quot(_dM-1|0,_dN)-1|0;}}},_dO=0,_dP=new T(function(){return B(_5x(_dO));}),_dQ=new T(function(){return die(_dP);}),_dR=function(_dS,_dT){var _dU=E(_dT);switch(_dU){case  -1:var _dV=E(_dS);if(_dV==( -2147483648)){return E(_dQ);}else{return new F(function(){return _dL(_dV, -1);});}break;case 0:return E(_5B);default:return new F(function(){return _dL(_dS,_dU);});}},_dW=function(_dX,_dY){return new F(function(){return _dR(E(_dX),E(_dY));});},_dZ=0,_e0=new T2(0,_dQ,_dZ),_e1=function(_e2,_e3){var _e4=E(_e2),_e5=E(_e3);switch(_e5){case  -1:var _e6=E(_e4);if(_e6==( -2147483648)){return E(_e0);}else{if(_e6<=0){if(_e6>=0){var _e7=quotRemI(_e6, -1);return new T2(0,_e7.a,_e7.b);}else{var _e8=quotRemI(_e6, -1);return new T2(0,_e8.a,_e8.b);}}else{var _e9=quotRemI(_e6-1|0, -1);return new T2(0,_e9.a-1|0,(_e9.b+( -1)|0)+1|0);}}break;case 0:return E(_5B);default:if(_e4<=0){if(_e4>=0){var _ea=quotRemI(_e4,_e5);return new T2(0,_ea.a,_ea.b);}else{if(_e5<=0){var _eb=quotRemI(_e4,_e5);return new T2(0,_eb.a,_eb.b);}else{var _ec=quotRemI(_e4+1|0,_e5);return new T2(0,_ec.a-1|0,(_ec.b+_e5|0)-1|0);}}}else{if(_e5>=0){if(_e4>=0){var _ed=quotRemI(_e4,_e5);return new T2(0,_ed.a,_ed.b);}else{if(_e5<=0){var _ee=quotRemI(_e4,_e5);return new T2(0,_ee.a,_ee.b);}else{var _ef=quotRemI(_e4+1|0,_e5);return new T2(0,_ef.a-1|0,(_ef.b+_e5|0)-1|0);}}}else{var _eg=quotRemI(_e4-1|0,_e5);return new T2(0,_eg.a-1|0,(_eg.b+_e5|0)+1|0);}}}},_eh=function(_ei,_ej){var _ek=_ei%_ej;if(_ei<=0){if(_ei>=0){return E(_ek);}else{if(_ej<=0){return E(_ek);}else{var _el=E(_ek);return (_el==0)?0:_el+_ej|0;}}}else{if(_ej>=0){if(_ei>=0){return E(_ek);}else{if(_ej<=0){return E(_ek);}else{var _em=E(_ek);return (_em==0)?0:_em+_ej|0;}}}else{var _en=E(_ek);return (_en==0)?0:_en+_ej|0;}}},_eo=function(_ep,_eq){var _er=E(_eq);switch(_er){case  -1:return E(_dZ);case 0:return E(_5B);default:return new F(function(){return _eh(E(_ep),_er);});}},_es=function(_et,_eu){var _ev=E(_et),_ew=E(_eu);switch(_ew){case  -1:var _ex=E(_ev);if(_ex==( -2147483648)){return E(_dQ);}else{return new F(function(){return quot(_ex, -1);});}break;case 0:return E(_5B);default:return new F(function(){return quot(_ev,_ew);});}},_ey=function(_ez,_eA){var _eB=E(_ez),_eC=E(_eA);switch(_eC){case  -1:var _eD=E(_eB);if(_eD==( -2147483648)){return E(_e0);}else{var _eE=quotRemI(_eD, -1);return new T2(0,_eE.a,_eE.b);}break;case 0:return E(_5B);default:var _eF=quotRemI(_eB,_eC);return new T2(0,_eF.a,_eF.b);}},_eG=function(_eH,_eI){var _eJ=E(_eI);switch(_eJ){case  -1:return E(_dZ);case 0:return E(_5B);default:return E(_eH)%_eJ;}},_eK=function(_eL){return new F(function(){return _bO(E(_eL));});},_eM=function(_eN){return new T2(0,E(B(_bO(E(_eN)))),E(_cT));},_eO=function(_eP,_eQ){return imul(E(_eP),E(_eQ))|0;},_eR=function(_eS,_eT){return E(_eS)+E(_eT)|0;},_eU=function(_eV,_eW){return E(_eV)-E(_eW)|0;},_eX=function(_eY){var _eZ=E(_eY);return (_eZ<0)? -_eZ:E(_eZ);},_f0=function(_f1){return new F(function(){return _5O(_f1);});},_f2=function(_f3){return  -E(_f3);},_f4= -1,_f5=0,_f6=1,_f7=function(_f8){var _f9=E(_f8);return (_f9>=0)?(E(_f9)==0)?E(_f5):E(_f6):E(_f4);},_fa={_:0,a:_eR,b:_eU,c:_eO,d:_f2,e:_eX,f:_f7,g:_f0},_fb=function(_fc,_fd){return E(_fc)==E(_fd);},_fe=function(_ff,_fg){return E(_ff)!=E(_fg);},_fh=new T2(0,_fb,_fe),_fi=function(_fj,_fk){var _fl=E(_fj),_fm=E(_fk);return (_fl>_fm)?E(_fl):E(_fm);},_fn=function(_fo,_fp){var _fq=E(_fo),_fr=E(_fp);return (_fq>_fr)?E(_fr):E(_fq);},_fs=function(_ft,_fu){return (_ft>=_fu)?(_ft!=_fu)?2:1:0;},_fv=function(_fw,_fx){return new F(function(){return _fs(E(_fw),E(_fx));});},_fy=function(_fz,_fA){return E(_fz)>=E(_fA);},_fB=function(_fC,_fD){return E(_fC)>E(_fD);},_fE=function(_fF,_fG){return E(_fF)<=E(_fG);},_fH=function(_fI,_fJ){return E(_fI)<E(_fJ);},_fK={_:0,a:_fh,b:_fv,c:_fH,d:_fE,e:_fB,f:_fy,g:_fi,h:_fn},_fL=new T3(0,_fa,_fK,_eM),_fM={_:0,a:_fL,b:_dK,c:_es,d:_eG,e:_dW,f:_eo,g:_ey,h:_e1,i:_eK},_fN=function(_fO,_fP){while(1){var _fQ=E(_fO);if(!_fQ._){var _fR=_fQ.a,_fS=E(_fP);if(!_fS._){var _fT=_fS.a;if(!(imul(_fR,_fT)|0)){return new T1(0,imul(_fR,_fT)|0);}else{_fO=new T1(1,I_fromInt(_fR));_fP=new T1(1,I_fromInt(_fT));continue;}}else{_fO=new T1(1,I_fromInt(_fR));_fP=_fS;continue;}}else{var _fU=E(_fP);if(!_fU._){_fO=_fQ;_fP=new T1(1,I_fromInt(_fU.a));continue;}else{return new T1(1,I_mul(_fQ.a,_fU.a));}}}},_fV=function(_fW,_fX,_fY){while(1){if(!(_fX%2)){var _fZ=B(_fN(_fW,_fW)),_g0=quot(_fX,2);_fW=_fZ;_fX=_g0;continue;}else{var _g1=E(_fX);if(_g1==1){return new F(function(){return _fN(_fW,_fY);});}else{var _fZ=B(_fN(_fW,_fW)),_g2=B(_fN(_fW,_fY));_fW=_fZ;_fX=quot(_g1-1|0,2);_fY=_g2;continue;}}}},_g3=function(_g4,_g5){while(1){if(!(_g5%2)){var _g6=B(_fN(_g4,_g4)),_g7=quot(_g5,2);_g4=_g6;_g5=_g7;continue;}else{var _g8=E(_g5);if(_g8==1){return E(_g4);}else{return new F(function(){return _fV(B(_fN(_g4,_g4)),quot(_g8-1|0,2),_g4);});}}}},_g9=function(_ga){return E(E(_ga).c);},_gb=function(_gc){return E(E(_gc).a);},_gd=function(_ge){return E(E(_ge).b);},_gf=function(_gg){return E(E(_gg).b);},_gh=function(_gi){return E(E(_gi).c);},_gj=function(_gk){return E(E(_gk).a);},_gl=new T1(0,0),_gm=new T1(0,2),_gn=function(_go){return E(E(_go).g);},_gp=function(_gq){return E(E(_gq).d);},_gr=function(_gs,_gt){var _gu=B(_cP(_gs)),_gv=new T(function(){return B(_cR(_gu));}),_gw=new T(function(){return B(A3(_gp,_gs,_gt,new T(function(){return B(A2(_gn,_gv,_gm));})));});return new F(function(){return A3(_gj,B(_gb(B(_gd(_gu)))),_gw,new T(function(){return B(A2(_gn,_gv,_gl));}));});},_gx=new T(function(){return B(unCStr("Negative exponent"));}),_gy=new T(function(){return B(err(_gx));}),_gz=function(_gA){return E(E(_gA).c);},_gB=function(_gC,_gD,_gE,_gF){var _gG=B(_cP(_gD)),_gH=new T(function(){return B(_cR(_gG));}),_gI=B(_gd(_gG));if(!B(A3(_gh,_gI,_gF,new T(function(){return B(A2(_gn,_gH,_gl));})))){if(!B(A3(_gj,B(_gb(_gI)),_gF,new T(function(){return B(A2(_gn,_gH,_gl));})))){var _gJ=new T(function(){return B(A2(_gn,_gH,_gm));}),_gK=new T(function(){return B(A2(_gn,_gH,_cT));}),_gL=B(_gb(_gI)),_gM=function(_gN,_gO,_gP){while(1){var _gQ=B((function(_gR,_gS,_gT){if(!B(_gr(_gD,_gS))){if(!B(A3(_gj,_gL,_gS,_gK))){var _gU=new T(function(){return B(A3(_gz,_gD,new T(function(){return B(A3(_gf,_gH,_gS,_gK));}),_gJ));});_gN=new T(function(){return B(A3(_g9,_gC,_gR,_gR));});_gO=_gU;_gP=new T(function(){return B(A3(_g9,_gC,_gR,_gT));});return __continue;}else{return new F(function(){return A3(_g9,_gC,_gR,_gT);});}}else{var _gV=_gT;_gN=new T(function(){return B(A3(_g9,_gC,_gR,_gR));});_gO=new T(function(){return B(A3(_gz,_gD,_gS,_gJ));});_gP=_gV;return __continue;}})(_gN,_gO,_gP));if(_gQ!=__continue){return _gQ;}}},_gW=function(_gX,_gY){while(1){var _gZ=B((function(_h0,_h1){if(!B(_gr(_gD,_h1))){if(!B(A3(_gj,_gL,_h1,_gK))){var _h2=new T(function(){return B(A3(_gz,_gD,new T(function(){return B(A3(_gf,_gH,_h1,_gK));}),_gJ));});return new F(function(){return _gM(new T(function(){return B(A3(_g9,_gC,_h0,_h0));}),_h2,_h0);});}else{return E(_h0);}}else{_gX=new T(function(){return B(A3(_g9,_gC,_h0,_h0));});_gY=new T(function(){return B(A3(_gz,_gD,_h1,_gJ));});return __continue;}})(_gX,_gY));if(_gZ!=__continue){return _gZ;}}};return new F(function(){return _gW(_gE,_gF);});}else{return new F(function(){return A2(_gn,_gC,_cT);});}}else{return E(_gy);}},_h3=new T(function(){return B(err(_gx));}),_h4=function(_h5,_h6){var _h7=B(_ap(_h6)),_h8=_h7.a,_h9=_h7.b,_ha=new T(function(){return B(_cR(new T(function(){return B(_cP(_h5));})));});if(_h9<0){var _hb= -_h9;if(_hb>=0){var _hc=E(_hb);if(!_hc){var _hd=E(_cT);}else{var _hd=B(_g3(_aG,_hc));}if(!B(_5G(_hd,_69))){var _he=B(_60(_h8,_hd));return new T2(0,new T(function(){return B(A2(_gn,_ha,_he.a));}),new T(function(){return B(_5C(_he.b,_h9));}));}else{return E(_5B);}}else{return E(_h3);}}else{var _hf=new T(function(){var _hg=new T(function(){return B(_gB(_ha,_fM,new T(function(){return B(A2(_gn,_ha,_aG));}),_h9));});return B(A3(_g9,_ha,new T(function(){return B(A2(_gn,_ha,_h8));}),_hg));});return new T2(0,_hf,_8W);}},_hh=function(_hi){return E(E(_hi).a);},_hj=function(_hk,_hl){var _hm=B(_h4(_hk,E(_hl))),_hn=_hm.a;if(E(_hm.b)<=0){return E(_hn);}else{var _ho=B(_cR(B(_cP(_hk))));return new F(function(){return A3(_hh,_ho,_hn,new T(function(){return B(A2(_gn,_ho,_4Q));}));});}},_hp=function(_hq,_hr){var _hs=B(_h4(_hq,E(_hr))),_ht=_hs.a;if(E(_hs.b)>=0){return E(_ht);}else{var _hu=B(_cR(B(_cP(_hq))));return new F(function(){return A3(_gf,_hu,_ht,new T(function(){return B(A2(_gn,_hu,_4Q));}));});}},_hv=function(_hw,_hx){var _hy=B(_h4(_hw,E(_hx)));return new T2(0,_hy.a,_hy.b);},_hz=function(_hA,_hB){var _hC=B(_h4(_hA,_hB)),_hD=_hC.a,_hE=E(_hC.b),_hF=new T(function(){var _hG=B(_cR(B(_cP(_hA))));if(_hE>=0){return B(A3(_hh,_hG,_hD,new T(function(){return B(A2(_gn,_hG,_4Q));})));}else{return B(A3(_gf,_hG,_hD,new T(function(){return B(A2(_gn,_hG,_4Q));})));}}),_hH=function(_hI){var _hJ=_hI-0.5;return (_hJ>=0)?(_hJ!=0)?E(_hF):(!B(_gr(_hA,_hD)))?E(_hF):E(_hD):E(_hD);};if(_hE!=0){if(_hE<=0){var _hK= -_hE-0.5;return (_hK>=0)?(_hK!=0)?E(_hF):(!B(_gr(_hA,_hD)))?E(_hF):E(_hD):E(_hD);}else{return new F(function(){return _hH(_hE);});}}else{return new F(function(){return _hH(0);});}},_hL=function(_hM,_hN){return new F(function(){return _hz(_hM,E(_hN));});},_hO=function(_hP,_hQ){return E(B(_h4(_hP,E(_hQ))).a);},_hR={_:0,a:_cO,b:_9x,c:_hv,d:_hO,e:_hL,f:_hj,g:_hp},_hS={_:0,a:_hR,b:_9Z,c:_aH,d:_aE,e:_aM,f:_as,g:_av,h:_aB,i:_bd,j:_ba,k:_aW,l:_aT,m:_aO,n:_aZ,o:_aR,p:_am},_hT=function(_hU){var _hV=E(_hU);if(!_hV._){var _hW=String(_hV.a);return E(_hW);}else{var _hX=I_toString(_hV.a);return E(_hX);}},_hY=1,_hZ=false,_i0=1,_i1=function(_i2){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_i2>=0){var _i3=jsShowI(_i2);return fromJSStr(_i3);}else{var _i4=jsShowI(_i2);return fromJSStr(_i4);}}))));});},_i5=function(_i6){var _i7=function(_i8){if(_i6<10){return new F(function(){return _i1(_i6);});}else{if(_i6>15){return new F(function(){return _i1(_i6);});}else{return (97+_i6|0)-10|0;}}};if(_i6<0){return new F(function(){return _i7(_);});}else{if(_i6>9){return new F(function(){return _i7(_);});}else{return 48+_i6|0;}}},_i9=function(_ia){return new F(function(){return _i5(E(_ia));});},_ib=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_ic=function(_id){return new F(function(){return _75(new T1(0,new T(function(){return B(_7i(_id,_ib));})),_6P);});},_ie=new T(function(){return B(_ic("GHC/Float.hs:622:11-64|d : ds\'"));}),_if=function(_ig,_ih){var _ii=E(_ih);return (_ii._==0)?__Z:new T2(1,new T(function(){return B(A1(_ig,_ii.a));}),new T(function(){return B(_if(_ig,_ii.b));}));},_ij=0,_ik=function(_il,_im){if(E(_il)<=0){var _in=B(_if(_i9,new T2(1,_ij,_im)));return (_in._==0)?E(_ie):new T2(0,_in.a,_in.b);}else{var _io=B(_if(_i9,_im));return (_io._==0)?E(_ie):new T2(0,_io.a,_io.b);}},_ip=function(_iq){return E(E(_iq).a);},_ir=function(_is){return E(E(_is).a);},_it=function(_iu){return E(E(_iu).a);},_iv=function(_iw){return E(E(_iw).a);},_ix=function(_iy){return E(E(_iy).b);},_iz=46,_iA=48,_iB=new T(function(){return B(unCStr("0"));}),_iC=function(_iD,_iE){while(1){var _iF=E(_iD);if(!_iF._){return E(_iE);}else{var _iG=new T2(1,_iF.a,_iE);_iD=_iF.b;_iE=_iG;continue;}}},_iH=function(_iI,_iJ,_iK){while(1){var _iL=B((function(_iM,_iN,_iO){var _iP=E(_iM);if(!_iP){var _iQ=B(_iC(_iN,_0));if(!_iQ._){return new F(function(){return _10(_iB,new T2(1,_iz,new T(function(){var _iR=E(_iO);if(!_iR._){return E(_iB);}else{return E(_iR);}})));});}else{return new F(function(){return _10(_iQ,new T2(1,_iz,new T(function(){var _iS=E(_iO);if(!_iS._){return E(_iB);}else{return E(_iS);}})));});}}else{var _iT=E(_iO);if(!_iT._){var _iU=new T2(1,_iA,_iN);_iI=_iP-1|0;_iJ=_iU;_iK=_0;return __continue;}else{var _iU=new T2(1,_iT.a,_iN);_iI=_iP-1|0;_iJ=_iU;_iK=_iT.b;return __continue;}}})(_iI,_iJ,_iK));if(_iL!=__continue){return _iL;}}},_iV=function(_iW,_iX){var _iY=jsShowI(_iW);return new F(function(){return _10(fromJSStr(_iY),_iX);});},_iZ=41,_j0=40,_j1=function(_j2,_j3,_j4){if(_j3>=0){return new F(function(){return _iV(_j3,_j4);});}else{if(_j2<=6){return new F(function(){return _iV(_j3,_j4);});}else{return new T2(1,_j0,new T(function(){var _j5=jsShowI(_j3);return B(_10(fromJSStr(_j5),new T2(1,_iZ,_j4)));}));}}},_j6=function(_j7){return new F(function(){return _j1(0,E(_j7),_0);});},_j8=function(_j9,_ja,_jb){return new F(function(){return _j1(E(_j9),E(_ja),_jb);});},_jc=function(_jd,_je){return new F(function(){return _j1(0,E(_jd),_je);});},_jf=function(_jg,_jh){return new F(function(){return _24(_jc,_jg,_jh);});},_ji=new T3(0,_j8,_j6,_jf),_jj=0,_jk=function(_jl,_jm,_jn){return new F(function(){return A1(_jl,new T2(1,_21,new T(function(){return B(A1(_jm,_jn));})));});},_jo=new T(function(){return B(unCStr(": empty list"));}),_jp=new T(function(){return B(unCStr("Prelude."));}),_jq=function(_jr){return new F(function(){return err(B(_10(_jp,new T(function(){return B(_10(_jr,_jo));},1))));});},_js=new T(function(){return B(unCStr("foldr1"));}),_jt=new T(function(){return B(_jq(_js));}),_ju=function(_jv,_jw){var _jx=E(_jw);if(!_jx._){return E(_jt);}else{var _jy=_jx.a,_jz=E(_jx.b);if(!_jz._){return E(_jy);}else{return new F(function(){return A2(_jv,_jy,new T(function(){return B(_ju(_jv,_jz));}));});}}},_jA=new T(function(){return B(unCStr(" out of range "));}),_jB=new T(function(){return B(unCStr("}.index: Index "));}),_jC=new T(function(){return B(unCStr("Ix{"));}),_jD=new T2(1,_iZ,_0),_jE=new T2(1,_iZ,_jD),_jF=0,_jG=function(_jH){return E(E(_jH).a);},_jI=function(_jJ,_jK,_jL,_jM,_jN){var _jO=new T(function(){var _jP=new T(function(){var _jQ=new T(function(){var _jR=new T(function(){var _jS=new T(function(){return B(A3(_ju,_jk,new T2(1,new T(function(){return B(A3(_jG,_jL,_jF,_jM));}),new T2(1,new T(function(){return B(A3(_jG,_jL,_jF,_jN));}),_0)),_jE));});return B(_10(_jA,new T2(1,_j0,new T2(1,_j0,_jS))));});return B(A(_jG,[_jL,_jj,_jK,new T2(1,_iZ,_jR)]));});return B(_10(_jB,new T2(1,_j0,_jQ)));},1);return B(_10(_jJ,_jP));},1);return new F(function(){return err(B(_10(_jC,_jO)));});},_jT=function(_jU,_jV,_jW,_jX,_jY){return new F(function(){return _jI(_jU,_jV,_jY,_jW,_jX);});},_jZ=function(_k0,_k1,_k2,_k3){var _k4=E(_k2);return new F(function(){return _jT(_k0,_k1,_k4.a,_k4.b,_k3);});},_k5=function(_k6,_k7,_k8,_k9){return new F(function(){return _jZ(_k9,_k8,_k7,_k6);});},_ka=new T(function(){return B(unCStr("Int"));}),_kb=function(_kc,_kd,_ke){return new F(function(){return _k5(_ji,new T2(0,_kd,_ke),_kc,_ka);});},_kf=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_kg=new T(function(){return B(err(_kf));}),_kh=1100,_ki=new T2(0,_ij,_kh),_kj=function(_kk){return new F(function(){return _k5(_ji,_ki,_kk,_ka);});},_kl=function(_){var _km=newArr(1101,_kg),_kn=_km,_ko=function(_kp,_){while(1){var _kq=B((function(_kr,_){if(0>_kr){return new F(function(){return _kj(_kr);});}else{if(_kr>1100){return new F(function(){return _kj(_kr);});}else{var _=_kn[_kr]=new T(function(){if(_kr>=0){var _ks=E(_kr);if(!_ks){return E(_cT);}else{return B(_g3(_aG,_ks));}}else{return E(_h3);}}),_kt=E(_kr);if(_kt==1100){return new T4(0,E(_ij),E(_kh),1101,_kn);}else{_kp=_kt+1|0;return __continue;}}}})(_kp,_));if(_kq!=__continue){return _kq;}}};return new F(function(){return _ko(0,_);});},_ku=function(_kv){var _kw=B(A1(_kv,_));return E(_kw);},_kx=new T(function(){return B(_ku(_kl));}),_ky=new T1(0,10),_kz=324,_kA=new T2(0,_ij,_kz),_kB=function(_kC){return new F(function(){return _k5(_ji,_kA,_kC,_ka);});},_kD=function(_){var _kE=newArr(325,_kg),_kF=_kE,_kG=function(_kH,_){while(1){var _kI=B((function(_kJ,_){if(0>_kJ){return new F(function(){return _kB(_kJ);});}else{if(_kJ>324){return new F(function(){return _kB(_kJ);});}else{var _=_kF[_kJ]=new T(function(){if(_kJ>=0){var _kK=E(_kJ);if(!_kK){return E(_cT);}else{return B(_g3(_ky,_kK));}}else{return E(_h3);}}),_kL=E(_kJ);if(_kL==324){return new T4(0,E(_ij),E(_kz),325,_kF);}else{_kH=_kL+1|0;return __continue;}}}})(_kH,_));if(_kI!=__continue){return _kI;}}};return new F(function(){return _kG(0,_);});},_kM=new T(function(){return B(_ku(_kD));}),_kN=function(_kO,_kP){var _kQ=function(_kR){if(!B(_5G(_kO,_ky))){if(_kP>=0){var _kS=E(_kP);if(!_kS){return E(_cT);}else{return new F(function(){return _g3(_kO,_kS);});}}else{return E(_h3);}}else{if(_kP>324){if(_kP>=0){var _kT=E(_kP);if(!_kT){return E(_cT);}else{return new F(function(){return _g3(_kO,_kT);});}}else{return E(_h3);}}else{var _kU=E(_kM),_kV=E(_kU.a),_kW=E(_kU.b);if(_kV>_kP){return new F(function(){return _kb(_kP,_kV,_kW);});}else{if(_kP>_kW){return new F(function(){return _kb(_kP,_kV,_kW);});}else{return E(_kU.d[_kP-_kV|0]);}}}}};if(!B(_5G(_kO,_aG))){return new F(function(){return _kQ(_);});}else{if(_kP<0){return new F(function(){return _kQ(_);});}else{if(_kP>1100){return new F(function(){return _kQ(_);});}else{var _kX=E(_kx),_kY=E(_kX.a),_kZ=E(_kX.b);if(_kY>_kP){return new F(function(){return _kb(_kP,_kY,_kZ);});}else{if(_kP>_kZ){return new F(function(){return _kb(_kP,_kY,_kZ);});}else{return E(_kX.d[_kP-_kY|0]);}}}}}},_l0=function(_l1){return E(E(_l1).f);},_l2=function(_l3){return E(E(_l3).d);},_l4=function(_l5){var _l6=E(_l5);if(!_l6._){return _l6.a;}else{return new F(function(){return I_toNumber(_l6.a);});}},_l7=function(_l8){return E(E(_l8).c);},_l9=function(_la){return E(E(_la).e);},_lb=new T2(1,_ij,_0),_lc=function(_ld,_le){while(1){var _lf=E(_ld);if(!_lf._){var _lg=E(_lf.a);if(_lg==( -2147483648)){_ld=new T1(1,I_fromInt( -2147483648));continue;}else{var _lh=E(_le);if(!_lh._){return new T1(0,quot(_lg,_lh.a));}else{_ld=new T1(1,I_fromInt(_lg));_le=_lh;continue;}}}else{var _li=_lf.a,_lj=E(_le);return (_lj._==0)?new T1(0,I_toInt(I_quot(_li,I_fromInt(_lj.a)))):new T1(1,I_quot(_li,_lj.a));}}},_lk=function(_ll,_lm,_ln){if(!B(A3(_gj,B(_gb(B(_gd(B(_iv(B(_it(_ll)))))))),_ln,new T(function(){return B(A2(_gn,B(_ir(B(_ip(B(_ix(_ll)))))),_69));})))){var _lo=new T(function(){return B(A2(_l7,_ll,_ln));}),_lp=new T(function(){return B(A2(_l2,_ll,_ln));}),_lq=new T(function(){return E(B(A2(_l9,_ll,_ln)).a)-E(_lp)|0;}),_lr=new T(function(){return B(A2(_l0,_ll,_ln));}),_ls=new T(function(){return E(E(_lr).b);}),_lt=new T(function(){var _lu=E(_ls),_lv=E(_lq)-_lu|0;if(_lv<=0){return new T2(0,new T(function(){return E(E(_lr).a);}),_lu);}else{return new T2(0,new T(function(){var _lw=B(_kN(_lo,_lv));if(!B(_5G(_lw,_69))){return B(_lc(E(_lr).a,_lw));}else{return E(_5B);}}),_lu+_lv|0);}}),_lx=new T(function(){return E(E(_lt).b);}),_ly=new T(function(){return E(E(_lt).a);}),_lz=new T(function(){var _lA=E(_lx);if(_lA<0){if(_lA<=E(_lq)){return new T4(0,new T(function(){return B(_fN(_ly,_aG));}),new T(function(){return B(_fN(B(_kN(_lo, -_lA)),_aG));}),_4Q,_4Q);}else{if(!B(_5G(_ly,B(_kN(_lo,E(_lp)-1|0))))){return new T4(0,new T(function(){return B(_fN(_ly,_aG));}),new T(function(){return B(_fN(B(_kN(_lo, -_lA)),_aG));}),_4Q,_4Q);}else{return new T4(0,new T(function(){return B(_fN(B(_fN(_ly,_lo)),_aG));}),new T(function(){return B(_fN(B(_kN(_lo, -_lA+1|0)),_aG));}),_lo,_4Q);}}}else{var _lB=new T(function(){return B(_kN(_lo,_lA));});if(!B(_5G(_ly,B(_kN(_lo,E(_lp)-1|0))))){return new T4(0,new T(function(){return B(_fN(B(_fN(_ly,_lB)),_aG));}),_aG,_lB,_lB);}else{return new T4(0,new T(function(){return B(_fN(B(_fN(B(_fN(_ly,_lB)),_lo)),_aG));}),new T(function(){return B(_fN(_aG,_lo));}),new T(function(){return B(_fN(_lB,_lo));}),_lB);}}}),_lC=new T(function(){return E(E(_lz).b);}),_lD=new T(function(){return E(E(_lz).c);}),_lE=new T(function(){return E(E(_lz).a);}),_lF=new T(function(){var _lG=new T(function(){return B(_5R(_lE,_lD));}),_lH=function(_lI){var _lJ=(Math.log(B(_l4(B(_5R(_ly,_4Q)))))+E(_lx)*Math.log(B(_l4(_lo))))/Math.log(B(_l4(_lm))),_lK=_lJ&4294967295;return (_lK>=_lJ)?E(_lK):_lK+1|0;},_lL=function(_lM){while(1){if(_lM<0){if(!B(_7V(B(_fN(B(_kN(_lm, -_lM)),_lG)),_lC))){var _lN=_lM+1|0;_lM=_lN;continue;}else{return E(_lM);}}else{if(!B(_7V(_lG,B(_fN(B(_kN(_lm,_lM)),_lC))))){var _lN=_lM+1|0;_lM=_lN;continue;}else{return E(_lM);}}}};if(!B(_5G(_lo,_aG))){return B(_lL(B(_lH(_))));}else{if(!B(_5G(_lm,_ky))){return B(_lL(B(_lH(_))));}else{var _lO=(E(_lp)-1|0)+E(_ls)|0;if(_lO<0){return B(_lL(quot(imul(_lO,8651)|0,28738)));}else{return B(_lL(quot(imul(_lO,8651)|0,28738)+1|0));}}}}),_lP=new T(function(){var _lQ=E(_lF),_lR=function(_lS,_lT,_lU,_lV,_lW){while(1){var _lX=B((function(_lY,_lZ,_m0,_m1,_m2){if(!B(_5G(_m0,_69))){var _m3=B(_60(B(_fN(_lZ,_lm)),_m0)),_m4=_m3.a,_m5=_m3.b,_m6=B(_fN(_m2,_lm)),_m7=B(_fN(_m1,_lm));if(!B(_6t(_m5,_m6))){if(!B(_6k(B(_5R(_m5,_m7)),_m0))){var _m8=new T2(1,_m4,_lY),_m9=_m0;_lS=_m8;_lT=_m5;_lU=_m9;_lV=_m7;_lW=_m6;return __continue;}else{return new T2(1,new T(function(){return B(_5R(_m4,_4Q));}),_lY);}}else{return (!B(_6k(B(_5R(_m5,_m7)),_m0)))?new T2(1,_m4,_lY):(!B(_6t(B(_fN(_m5,_aG)),_m0)))?new T2(1,new T(function(){return B(_5R(_m4,_4Q));}),_lY):new T2(1,_m4,_lY);}}else{return E(_5B);}})(_lS,_lT,_lU,_lV,_lW));if(_lX!=__continue){return _lX;}}};if(_lQ<0){var _ma=B(_kN(_lm, -_lQ));return B(_if(_f0,B(_iC(B(_lR(_0,B(_fN(_lE,_ma)),_lC,B(_fN(_lD,_ma)),B(_fN(E(_lz).d,_ma)))),_0))));}else{return B(_if(_f0,B(_iC(B(_lR(_0,_lE,B(_fN(_lC,B(_kN(_lm,_lQ)))),_lD,E(_lz).d)),_0))));}});return new T2(0,_lP,_lF);}else{return new T2(0,_lb,_ij);}},_mb=function(_mc){var _md=E(_mc);return (_md==1)?E(_lb):new T2(1,_ij,new T(function(){return B(_mb(_md-1|0));}));},_me=true,_mf=function(_mg,_mh){while(1){var _mi=E(_mh);if(!_mi._){return true;}else{if(!B(A1(_mg,_mi.a))){return false;}else{_mh=_mi.b;continue;}}}},_mj=function(_mk){return (E(_mk)%2==0)?true:false;},_ml=new T(function(){return B(unCStr("roundTo: bad Value"));}),_mm=new T(function(){return B(err(_ml));}),_mn=function(_mo){return (E(_mo)==0)?true:false;},_mp=function(_mq,_mr,_ms){var _mt=new T(function(){return quot(E(_mq),2);}),_mu=function(_mv,_mw,_mx){var _my=E(_mx);if(!_my._){return new T2(0,_ij,new T(function(){var _mz=E(_mv);if(0>=_mz){return __Z;}else{return B(_mb(_mz));}}));}else{var _mA=_my.a,_mB=_my.b,_mC=E(_mv);if(!_mC){var _mD=E(_mA),_mE=E(_mt);return (_mD!=_mE)?new T2(0,new T(function(){if(_mD<_mE){return E(_ij);}else{return E(_i0);}}),_0):(!E(_mw))?new T2(0,new T(function(){if(_mD<_mE){return E(_ij);}else{return E(_i0);}}),_0):(!B(_mf(_mn,_mB)))?new T2(0,new T(function(){if(_mD<_mE){return E(_ij);}else{return E(_i0);}}),_0):new T2(0,_ij,_0);}else{var _mF=B(_mu(_mC-1|0,new T(function(){return B(_mj(_mA));},1),_mB)),_mG=_mF.b,_mH=E(_mF.a)+E(_mA)|0;return (_mH!=E(_mq))?new T2(0,_ij,new T2(1,_mH,_mG)):new T2(0,_i0,new T2(1,_ij,_mG));}}},_mI=B(_mu(_mr,_me,_ms)),_mJ=_mI.a,_mK=_mI.b;switch(E(_mJ)){case 0:return new T2(0,_mJ,_mK);case 1:return new T2(0,_i0,new T2(1,_i0,_mK));default:return E(_mm);}},_mL=function(_mM,_mN){var _mO=E(_mN);if(!_mO._){return new T2(0,_0,_0);}else{var _mP=_mO.a,_mQ=_mO.b,_mR=E(_mM);if(_mR==1){return new T2(0,new T2(1,_mP,_0),_mQ);}else{var _mS=new T(function(){var _mT=B(_mL(_mR-1|0,_mQ));return new T2(0,_mT.a,_mT.b);});return new T2(0,new T2(1,_mP,new T(function(){return E(E(_mS).a);})),new T(function(){return E(E(_mS).b);}));}}},_mU=new T(function(){return B(unCStr("e0"));}),_mV=new T2(1,_iA,_mU),_mW=function(_mX){var _mY=E(_mX);return (_mY==1)?E(_mV):new T2(1,_iA,new T(function(){return B(_mW(_mY-1|0));}));},_mZ=0,_n0=10,_n1=function(_n2,_n3){var _n4=E(_n3);return (_n4._==0)?__Z:new T2(1,_n2,new T(function(){return B(_n1(_n4.a,_n4.b));}));},_n5=new T(function(){return B(unCStr("init"));}),_n6=new T(function(){return B(_jq(_n5));}),_n7=function(_n8){return E(E(_n8).l);},_n9=function(_na){return E(E(_na).k);},_nb=function(_nc){return E(E(_nc).n);},_nd=new T(function(){return B(unCStr("NaN"));}),_ne=new T(function(){return B(unCStr("-Infinity"));}),_nf=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_ng=new T(function(){return B(err(_nf));}),_nh=new T(function(){return B(unCStr("Infinity"));}),_ni=new T2(1,_iz,_0),_nj=101,_nk=new T(function(){return B(_ic("GHC/Float.hs:594:12-70|(d : ds\')"));}),_nl=new T(function(){return B(unCStr("0.0e0"));}),_nm=function(_nn){return E(E(_nn).d);},_no=45,_np=function(_nq,_nr,_ns,_nt,_nu){if(!B(A2(_n9,_nq,_nu))){var _nv=new T(function(){return B(_ir(new T(function(){return B(_ip(new T(function(){return B(_ix(_nq));})));})));});if(!B(A2(_n7,_nq,_nu))){var _nw=function(_nx,_ny,_nz){while(1){var _nA=B((function(_nB,_nC,_nD){switch(E(_nB)){case 0:var _nE=E(_ns);if(!_nE._){var _nF=B(_if(_i9,_nC));if(!_nF._){return E(_ng);}else{var _nG=_nF.b,_nH=E(_nF.a),_nI=function(_nJ){var _nK=E(_nG);if(!_nK._){var _nL=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_j1(0,E(_nD)-1|0,_0));})));});return new T2(1,_nH,_nL);}else{var _nM=new T(function(){var _nN=new T(function(){return B(unAppCStr("e",new T(function(){return B(_j1(0,E(_nD)-1|0,_0));})));},1);return B(_10(_nK,_nN));});return new T2(1,_nH,new T2(1,_iz,_nM));}};if(E(_nH)==48){if(!E(_nG)._){return E(_nl);}else{return new F(function(){return _nI(_);});}}else{return new F(function(){return _nI(_);});}}}else{var _nO=new T(function(){var _nP=E(_nE.a);if(_nP>1){return E(_nP);}else{return E(_i0);}}),_nQ=function(_nR){var _nS=new T(function(){var _nT=B(_mp(_n0,new T(function(){return E(_nO)+1|0;},1),_nC));return new T2(0,_nT.a,_nT.b);}),_nU=new T(function(){return E(E(_nS).a);}),_nV=new T(function(){if(E(_nU)<=0){var _nW=B(_if(_i9,E(_nS).b));if(!_nW._){return E(_nk);}else{return new T2(0,_nW.a,_nW.b);}}else{var _nX=E(E(_nS).b);if(!_nX._){return E(_n6);}else{var _nY=B(_if(_i9,B(_n1(_nX.a,_nX.b))));if(!_nY._){return E(_nk);}else{return new T2(0,_nY.a,_nY.b);}}}}),_nZ=new T(function(){return B(_10(E(_nV).b,new T2(1,_nj,new T(function(){return B(_j1(0,(E(_nD)-1|0)+E(_nU)|0,_0));}))));});return new T2(1,new T(function(){return E(E(_nV).a);}),new T2(1,_iz,_nZ));},_o0=E(_nC);if(!_o0._){return new F(function(){return _nQ(_);});}else{if(!E(_o0.a)){if(!E(_o0.b)._){return new T2(1,_iA,new T2(1,_iz,new T(function(){var _o1=E(_nO);if(0>=_o1){return E(_mU);}else{return B(_mW(_o1));}})));}else{return new F(function(){return _nQ(_);});}}else{return new F(function(){return _nQ(_);});}}}break;case 1:var _o2=E(_ns);if(!_o2._){var _o3=E(_nD);if(_o3>0){return new F(function(){return _iH(_o3,_0,new T(function(){return B(_if(_i9,_nC));},1));});}else{var _o4=new T(function(){var _o5= -_o3;if(0>=_o5){return B(_if(_i9,_nC));}else{var _o6=new T(function(){return B(_if(_i9,_nC));}),_o7=function(_o8){var _o9=E(_o8);return (_o9==1)?E(new T2(1,_iA,_o6)):new T2(1,_iA,new T(function(){return B(_o7(_o9-1|0));}));};return B(_o7(_o5));}});return new F(function(){return unAppCStr("0.",_o4);});}}else{var _oa=_o2.a,_ob=E(_nD);if(_ob<0){var _oc=new T(function(){var _od= -_ob;if(0>=_od){var _oe=B(_mp(_n0,new T(function(){var _of=E(_oa);if(_of>0){return E(_of);}else{return E(_ij);}},1),_nC));return B(_ik(_oe.a,_oe.b));}else{var _og=function(_oh){var _oi=E(_oh);return (_oi==1)?E(new T2(1,_ij,_nC)):new T2(1,_ij,new T(function(){return B(_og(_oi-1|0));}));},_oj=B(_mp(_n0,new T(function(){var _ok=E(_oa);if(_ok>0){return E(_ok);}else{return E(_ij);}},1),B(_og(_od))));return B(_ik(_oj.a,_oj.b));}});return new T2(1,new T(function(){return E(E(_oc).a);}),new T(function(){var _ol=E(E(_oc).b);if(!_ol._){if(!E(_nt)){return __Z;}else{return E(_ni);}}else{return new T2(1,_iz,_ol);}}));}else{var _om=B(_mp(_n0,new T(function(){var _on=E(_oa);if(_on>0){return _on+_ob|0;}else{return E(_ob);}},1),_nC)),_oo=_om.b,_op=_ob+E(_om.a)|0;if(_op>0){var _oq=B(_mL(_op,B(_if(_i9,_oo)))),_or=_oq.b,_os=E(_oq.a);if(!_os._){return new F(function(){return _10(_iB,new T(function(){var _ot=E(_or);if(!_ot._){if(!E(_nt)){return __Z;}else{return E(_ni);}}else{return new T2(1,_iz,_ot);}},1));});}else{return new F(function(){return _10(_os,new T(function(){var _ou=E(_or);if(!_ou._){if(!E(_nt)){return __Z;}else{return E(_ni);}}else{return new T2(1,_iz,_ou);}},1));});}}else{return new F(function(){return _10(_iB,new T(function(){var _ov=B(_if(_i9,_oo));if(!_ov._){if(!E(_nt)){return __Z;}else{return E(_ni);}}else{return new T2(1,_iz,_ov);}},1));});}}}break;default:var _ow=E(_nD);if(_ow>=0){if(_ow<=7){var _ox=_nC;_nx=_hY;_ny=_ox;_nz=_ow;return __continue;}else{var _ox=_nC;_nx=_mZ;_ny=_ox;_nz=_ow;return __continue;}}else{var _ox=_nC;_nx=_mZ;_ny=_ox;_nz=_ow;return __continue;}}})(_nx,_ny,_nz));if(_nA!=__continue){return _nA;}}},_oy=function(_oz){var _oA=new T(function(){var _oB=B(_lk(_nq,_ky,new T(function(){return B(A2(_nm,_nv,_nu));})));return B(_nw(_nr,_oB.a,_oB.b));});return new T2(1,_no,_oA);};if(!B(A3(_gh,B(_gd(B(_iv(B(_it(_nq)))))),_nu,new T(function(){return B(A2(_gn,_nv,_69));})))){if(!B(A2(_nb,_nq,_nu))){var _oC=B(_lk(_nq,_ky,_nu));return new F(function(){return _nw(_nr,_oC.a,_oC.b);});}else{return new F(function(){return _oy(_);});}}else{return new F(function(){return _oy(_);});}}else{return (!B(A3(_gh,B(_gd(B(_iv(B(_it(_nq)))))),_nu,new T(function(){return B(A2(_gn,_nv,_69));}))))?E(_nh):E(_ne);}}else{return E(_nd);}},_oD=1,_oE=new T1(1,_oD),_oF=new T1(0,0),_oG=function(_oH){var _oI=B(_ap(_oH)),_oJ=_oI.a,_oK=_oI.b,_oL=function(_oM,_oN){if(_oN>=0.1){return new F(function(){return _np(_hS,_hY,_oE,_hZ,_oH);});}else{return new F(function(){return fromJSStr(B(_hT(_oM)));});}};if(_oK>=0){return new F(function(){return _oL(new T(function(){return B(_6a(_oJ,_oK));},1),0);});}else{var _oO= -_oK;if(_oO<=52){if(!B(_6t(_oJ,_oF))){var _oP=B(_cv(_oJ)),_oQ=hs_uncheckedIShiftRA64(_oP,_oO),_oR=hs_uncheckedIShiftL64(_oQ,_oO),_oS=hs_minusInt64(_oP,_oR);return new F(function(){return _oL(new T(function(){return B(_bQ(_oQ));},1),B(_5C(B(_bQ(_oS)),_oK)));});}else{var _oT=B(_cv(B(_8P(_oJ)))),_oU=hs_uncheckedIShiftRA64(_oT,_oO),_oV=hs_uncheckedIShiftL64(_oU,_oO),_oW=hs_minusInt64(_oT,_oV),_oX=hs_negateInt64(_oW);return new F(function(){return _oL(new T(function(){var _oY=hs_negateInt64(_oU);return B(_bQ(_oY));},1),B(_5C(B(_bQ(_oX)),_oK)));});}}else{return new F(function(){return _oL(_oF,_oH);});}}},_oZ=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_p0=new T(function(){return B(unCStr("value"));}),_p1=function(_p2,_p3,_p4,_p5,_p6,_p7,_p8,_){switch(E(_p2)){case 0:var _p9=toJSStr(E(_p0)),_pa=E(_oZ),_pb=__app3(_pa,E(_p4),_p9,toJSStr(B(_oG(E(_p7))))),_pc=__app3(_pa,E(_p5),_p9,toJSStr(B(_oG(E(_p8)))));return new F(function(){return _4C(_);});break;case 1:var _pd=toJSStr(E(_p0)),_pe=E(_oZ),_pf=__app3(_pe,E(_p3),_pd,toJSStr(B(_oG(E(_p6))))),_pg=__app3(_pe,E(_p4),_pd,toJSStr(B(_oG(E(_p7)))));return new F(function(){return _4C(_);});break;default:var _ph=toJSStr(E(_p0)),_pi=E(_oZ),_pj=__app3(_pi,E(_p3),_ph,toJSStr(B(_oG(E(_p6))))),_pk=__app3(_pi,E(_p5),_ph,toJSStr(B(_oG(E(_p8)))));return new F(function(){return _4C(_);});}},_pl=new T(function(){return B(unCStr("img"));}),_pm=new T(function(){return B(unCStr("screen-disabled"));}),_pn=new T(function(){return eval("(function(e,c,x){x?e.classList.add(c):e.classList.remove(c);})");}),_po=function(_pp,_pq,_){var _pr=B(_43(_pp,_)),_ps=_pr,_pt=E(_pq),_pu=E(_2I),_pv=__app2(_pu,_pt,toJSStr(E(_pl))),_pw=__arr2lst(0,_pv),_px=B(_1(_pw,_)),_py=function(_,_pz){var _pA=__app2(_pu,_pt,toJSStr(B(unAppCStr(".js-",_ps)))),_pB=__arr2lst(0,_pA),_pC=B(_1(_pB,_)),_pD=E(_pC);if(!_pD._){return _3l;}else{var _pE=E(_pm),_pF=E(_pn),_pG=__app3(_pF,E(_pD.a),toJSStr(_pE),false),_pH=function(_pI,_){while(1){var _pJ=E(_pI);if(!_pJ._){return _3l;}else{var _pK=__app3(_pF,E(_pJ.a),toJSStr(_pE),false);_pI=_pJ.b;continue;}}};return new F(function(){return _pH(_pD.b,_);});}},_pL=E(_px);if(!_pL._){return new F(function(){return _py(_,_3l);});}else{var _pM=E(_pm),_pN=E(_pn),_pO=__app3(_pN,E(_pL.a),toJSStr(_pM),true),_pP=function(_pQ,_){while(1){var _pR=E(_pQ);if(!_pR._){return _3l;}else{var _pS=__app3(_pN,E(_pR.a),toJSStr(_pM),true);_pQ=_pR.b;continue;}}},_pT=B(_pP(_pL.b,_));return new F(function(){return _py(_,_pT);});}},_pU=new T(function(){return B(unCStr("in"));}),_pV=new T(function(){return B(unCStr("cm"));}),_pW=function(_pX,_pY,_){var _pZ=B(_43(_pY,_)),_q0=E(_pX),_q1=B(_47(_4e,_q0,_)),_q2=E(_q1),_q3=function(_q4){var _q5=__app3(E(_oZ),_q0,toJSStr(E(_p0)),toJSStr(B(_oG(_q4))));return new F(function(){return _4C(_);});};if(!B(_4f(_pZ,_pV))){if(!B(_4f(_pZ,_pU))){return new F(function(){return _q3(_q2);});}else{return new F(function(){return _q3(_q2*0.39370078740157477);});}}else{return new F(function(){return _q3(_q2*2.54);});}},_q6=2,_q7=1,_q8=0,_q9=2,_qa=1,_qb=function(_qc){return E(E(_qc).a);},_qd=function(_qe){return E(E(_qe).a);},_qf=function(_qg){return E(E(_qg).b);},_qh=function(_qi){return E(E(_qi).b);},_qj=function(_qk){return E(E(_qk).a);},_ql=function(_){return new F(function(){return nMV(_2m);});},_qm=function(_qn){var _qo=B(A1(_qn,_));return E(_qo);},_qp=new T(function(){return B(_qm(_ql));}),_qq=function(_){return new F(function(){return __jsNull();});},_qr=new T(function(){return B(_qm(_qq));}),_qs=new T(function(){return E(_qr);}),_qt=function(_qu){return E(E(_qu).b);},_qv=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_qw=function(_qx){return E(E(_qx).d);},_qy=function(_qz,_qA,_qB,_qC,_qD,_qE){var _qF=B(_qb(_qz)),_qG=B(_qd(_qF)),_qH=new T(function(){return B(_2J(_qF));}),_qI=new T(function(){return B(_qw(_qG));}),_qJ=new T(function(){return B(A1(_qA,_qC));}),_qK=new T(function(){return B(A2(_qj,_qB,_qD));}),_qL=function(_qM){return new F(function(){return A1(_qI,new T3(0,_qK,_qJ,_qM));});},_qN=function(_qO){var _qP=new T(function(){var _qQ=new T(function(){var _qR=__createJSFunc(2,function(_qS,_){var _qT=B(A2(E(_qO),_qS,_));return _qs;}),_qU=_qR;return function(_){return new F(function(){return __app3(E(_qv),E(_qJ),E(_qK),_qU);});};});return B(A1(_qH,_qQ));});return new F(function(){return A3(_qf,_qG,_qP,_qL);});},_qV=new T(function(){var _qW=new T(function(){return B(_2J(_qF));}),_qX=function(_qY){var _qZ=new T(function(){return B(A1(_qW,function(_){var _=wMV(E(_qp),new T1(1,_qY));return new F(function(){return A(_qh,[_qB,_qD,_qY,_]);});}));});return new F(function(){return A3(_qf,_qG,_qZ,_qE);});};return B(A2(_qt,_qz,_qX));});return new F(function(){return A3(_qf,_qG,_qV,_qN);});},_r0=function(_r1,_){var _r2=function(_r3,_){var _r4=E(_r1),_r5=_r4.b,_r6=_r4.c,_r7=_r4.d,_r8=E(_r4.a),_r9=B(_po(_r8,_r4.e,_)),_ra=B(_4t(_r8,_r5,_r6,_r7,_)),_rb=E(_ra),_rc=_rb.a,_rd=_rb.b,_re=new T(function(){var _rf=E(_rd),_rg=E(_rc);return Math.sqrt(_rf*_rf/(1+_rg*_rg));});return new F(function(){return _p1(_q8,_r5,_r6,_r7,_rd,new T(function(){return E(_re)*E(_rc);},1),_re,_);});},_rh=B(A(_qy,[_40,_3Y,_3A,new T(function(){return E(E(_r1).a);}),_q9,_r2,_])),_ri=function(_rj,_){var _rk=E(_r1),_rl=_rk.b,_rm=_rk.c,_rn=_rk.d,_ro=B(_pW(_rl,E(_rk.f),_)),_rp=B(_4t(E(_rk.a),_rl,_rm,_rn,_)),_rq=E(_rp),_rr=_rq.a,_rs=_rq.b,_rt=new T(function(){var _ru=E(_rs),_rv=E(_rr);return Math.sqrt(_ru*_ru/(1+_rv*_rv));});return new F(function(){return _p1(_q8,_rl,_rm,_rn,_rs,new T(function(){return E(_rt)*E(_rr);},1),_rt,_);});},_rw=B(A(_qy,[_40,_3Y,_3A,new T(function(){return E(E(_r1).f);}),_q9,_ri,_])),_rx=function(_ry,_){var _rz=E(_r1),_rA=_rz.b,_rB=_rz.c,_rC=_rz.d,_rD=B(_4t(E(_rz.a),_rA,_rB,_rC,_)),_rE=E(_rD),_rF=_rE.a,_rG=_rE.b,_rH=new T(function(){var _rI=E(_rG),_rJ=E(_rF);return Math.sqrt(_rI*_rI/(1+_rJ*_rJ));});return new F(function(){return _p1(_q8,_rA,_rB,_rC,_rG,new T(function(){return E(_rH)*E(_rF);},1),_rH,_);});},_rK=B(A(_qy,[_40,_3Y,_3X,new T(function(){return E(E(_r1).b);}),_qa,_rx,_])),_rL=function(_rM,_){var _rN=E(_r1),_rO=_rN.b,_rP=_rN.c,_rQ=_rN.d,_rR=B(_4t(E(_rN.a),_rO,_rP,_rQ,_)),_rS=E(_rR),_rT=_rS.c,_rU=new T(function(){return E(_rT)*(1/E(_rS.a));});return new F(function(){return _p1(_q6,_rO,_rP,_rQ,new T(function(){var _rV=E(_rT),_rW=E(_rU);return Math.sqrt(_rV*_rV+_rW*_rW);},1),_rT,_rU,_);});},_rX=B(A(_qy,[_40,_3Y,_3X,new T(function(){return E(E(_r1).c);}),_qa,_rL,_])),_rY=function(_rZ,_){var _s0=E(_r1),_s1=_s0.b,_s2=_s0.c,_s3=_s0.d,_s4=B(_4t(E(_s0.a),_s1,_s2,_s3,_)),_s5=E(_s4),_s6=_s5.d,_s7=new T(function(){return E(_s6)*E(_s5.a);});return new F(function(){return _p1(_q7,_s1,_s2,_s3,new T(function(){var _s8=E(_s7),_s9=E(_s6);return Math.sqrt(_s8*_s8+_s9*_s9);},1),_s7,_s6,_);});};return new F(function(){return A(_qy,[_40,_3Y,_3X,new T(function(){return E(E(_r1).d);}),_qa,_rY,_]);});},_sa=function(_sb,_){while(1){var _sc=E(_sb);if(!_sc._){return _3l;}else{var _sd=B(_r0(_sc.a,_));_sb=_sc.b;continue;}}},_se=function(_){var _sf=B(_3g(_));return new F(function(){return _sa(_sf,_);});},_sg=function(_){return new F(function(){return _se(_);});};
var hasteMain = function() {B(A(_sg, [0]));};window.onload = hasteMain;