import random
import sys

import jpamb
import jvm
import jvm.state as jvmc
import z3

def binary(op, v1: int, v2: int) -> int | str:
    match op:
        case jvm.BinaryOpr.Div:
            try:
                return v1 // v2
            except ZeroDivisionError:
                return "divide by zero"
        case jvm.BinaryOpr.Add:
            return v1 + v2
        case jvm.BinaryOpr.Sub:
            return v1 - v2
        case jvm.BinaryOpr.Mul:
            return v1 * v2
        case jvm.BinaryOpr.Rem:
            return v1 % v2
        case a:
            raise NotImplementedError(f"Unhandled binary {op!r}")


def compare(op, v1: int, v2: int) -> bool:
    match op:
        case jvm.CmpOpr.Eq:
            return v1 == v2
        case jvm.CmpOpr.Gt:
            return v1 > v2
        case jvm.CmpOpr.Ne:
            return v1 != v2
        case jvm.CmpOpr.Ge:
            return v1 >= v2
        case jvm.CmpOpr.Lt:
            return v1 < v2
        case jvm.CmpOpr.Le:
            return v1 <= v2
        case _:
            raise NotImplementedError(f"Unhandled comparation {op!r}")


def step(bc: jpamb.Bytecode, state: jvmc.State) -> tuple[jvmc.PC, jvmc.State | str]:
    assert isinstance(state, jvmc.State), f"expected state but got {state}"
    frame = state.frames.peek()
    pc = frame.pc
    opr = bc[pc]
    output = state
    print(f"Stepping {pc}:\n > {opr}", file=sys.stderr)
    match opr:
        case jvm.Push(type=t, value=v):
            if t is jvm.Int():
                frame.stack.push(jvmc.StackInt(v))
            elif t is jvm.Reference():
                assert isinstance(v, int), f"expected int, but got {v}"
                frame.stack.push(jvmc.StackReference(v))
            elif isinstance(t, jvm.Object):
                if t.name == jvm.ClassName("java.lang.String"):
                    assert isinstance(v, str), f"expected str, but got {v}"
                    # Push the string to the heap and a reference to it on the stack
                    ref = state.heap.new(jvmc.HeapString(v))
                    frame.stack.push(ref)
                else:
                    raise NotImplementedError(f"Unhandled object type {t}")
            else:
                raise NotImplementedError(f"Error {t}, {v}")
            frame.pc += 1

        case jvm.Binary(type=jvm.Int(), operant=op):
            v2, v1 = frame.stack.pop(), frame.stack.pop()
            assert isinstance(v1, jvmc.StackInt), f"expected int, but got {v1}"
            assert isinstance(v2, jvmc.StackInt), f"expected int, but got {v2}"

            value = binary(op, v1.value, v2.value)

            if isinstance(value, str):
                output = value
            else:
                frame.stack.push(jvmc.StackInt(value))
                frame.pc += 1

        # From the Lecture Notes:
        # https://courses.compute.dtu.dk/02242/topics/semantics.html
        # What are the Semantics of the JVM? (4)
        case jvm.Return(type=jvm.Int()):
            v1 = frame.stack.pop()
            state.frames.pop()
            if state.frames:
                frame = state.frames.peek()
                frame.stack.push(v1)
                frame.pc += 1
            else:
                output = "ok"

        case jvm.Return(type=None):
            state.frames.pop()
            if state.frames:
                frame = state.frames.peek()
                frame.pc += 1
            else:
                output = "ok"

        case jvm.Return(type=jvm.Reference()):
            v1 = frame.stack.pop()
            state.frames.pop()
            if state.frames:
                frame = state.frames.peek()
                frame.stack.push(v1)
                frame.pc += 1
            else:
                output = "ok"

        case jvm.Get(static=True, field=field):
            # Hack - Only handle the assertion case
            assert field.extension.name == "$assertionsDisabled"

            # Hack - Assuming assertions are never disabled
            frame.stack.push(jvmc.StackInt(0))
            frame.pc += 1

        case jvm.New(classname=jvm.ClassName("java.lang.AssertionError")):
            # Hack -- if we create an assertion error, we probably also throw it.
            output = "assertion error"

        # MY IMPLEMETED INSTRUCTIONS
        case jvm.Dup(words=words):
            # TODO: There is a `words` parameter. Not sure if we need to handle words > 1 differently
            if words != 1:
                raise NotImplementedError("Dup with words > 1 not implemented")

            value = frame.stack.pop()
            frame.stack.push(value)
            frame.stack.push(value)
            frame.pc += 1

        case jvm.Ifz(condition=op, target=target):  # From Activity 7 hint
            value = frame.stack.pop()
            # TODO: The specification also states that Ifz can be used for null checks
            assert isinstance(value, jvmc.StackInt), f"expected int, but got {value}"

            if compare(op, value.value, 0):
                frame.pc %= target  # Modulo used to return a new PC with the same methodId but new offset
            else:
                frame.pc += 1

        case jvm.If(condition=op, target=target):
            v2, v1 = frame.stack.pop(), frame.stack.pop()
            assert isinstance(v1, jvmc.StackInt), f"expected int, but got {v1}"
            assert isinstance(v2, jvmc.StackInt), f"expected int, but got {v2}"

            if compare(op, v1.value, v2.value):
                frame.pc %= target  # Modulo used to return a new PC with the same methodId but new offset
            else:
                frame.pc += 1

        case jvm.Load(type=jvm.Int(), index=i):
            v = frame.locals[i]
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            frame.stack.push(v)
            frame.pc += 1

        case jvm.Load(type=jvm.Reference(), index=i):
            v = frame.locals[i]
            assert isinstance(v, jvmc.StackReference), (
                f"expected StackReference, but got {v}"
            )
            frame.stack.push(v)
            frame.pc += 1

        case jvm.Store(type=type, index=i):
            v = frame.stack.pop()
            if isinstance(type, jvm.Int):
                assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            # TODO: Should we do more type assertions?
            frame.locals[i] = v
            frame.pc += 1

        case jvm.Incr(index=i, amount=amount):
            v = frame.locals[i]
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            frame.locals[i] = jvmc.StackInt(v.value + amount)
            frame.pc += 1

        case jvm.Goto(target=target):
            frame.pc %= target  # Modulo used to return a new PC with the same methodId but new offset

        case jvm.Cast(from_=jvm.Int(), to_=jvm.Short()):
            v = frame.stack.pop()
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            frame.stack.push(
                jvmc.StackInt(v.value & 0xFFFF)
            )  # TODO: Is this the correct way to truncate
            frame.pc += 1

        case jvm.NewArray(type=type, dim=1):
            count = frame.stack.pop()
            assert isinstance(count, jvmc.StackInt), f"expected int, but got {count}"
            array = jvmc.HeapArray(
                type, [0] * count.value
            )  # TODO: How do we handle i.e. floats?
            ref = state.heap.new(array)
            frame.stack.push(ref)
            frame.pc += 1

        case jvm.ArrayStore(type=jvm.Int()):  # TODO: For other than int?
            v, index, arrayref = frame.stack.pop(), frame.stack.pop(), frame.stack.pop()
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            assert isinstance(index, jvmc.StackInt), f"expected int, but got {index}"
            assert isinstance(arrayref, jvmc.StackReference), (
                f"expected arrayref to be StackReference, but got {arrayref}"
            )
            # Check for null-reference
            if arrayref.value == 0:
                output = "null pointer"
            else:
                array = state.heap.memory[arrayref.value - 1]
                assert isinstance(array, jvmc.HeapArray), (
                    f"expected HeapArray, but got {array}"
                )
                # Check for out of bounds
                if not (0 <= index.value and index.value < len(array.values)):
                    output = "out of bounds"
                else:
                    array.values[index.value] = v.value
                    frame.pc += 1

        case jvm.ArrayLength():
            arrayref = frame.stack.pop()
            assert isinstance(arrayref, jvmc.StackReference), (
                f"expected arrayref to be StackReference, but got {arrayref}"
            )
            if arrayref.value == 0:
                output = "null pointer"
            else:
                array = state.heap.memory[arrayref.value - 1]
                assert isinstance(array, jvmc.HeapArray), (
                    f"expected HeapArray, but got {array}"
                )
                length = len(array.values)
                frame.stack.push(jvmc.StackInt(length))
                frame.pc += 1

        case jvm.ArrayLoad(type=jvm.Int()) | jvm.ArrayLoad(type=jvm.Char()):
            index, arrayref = frame.stack.pop(), frame.stack.pop()
            assert isinstance(index, jvmc.StackInt), f"expected int, but got {index}"
            assert isinstance(arrayref, jvmc.StackReference), (
                f"expected arrayref to be StackReference, but got {arrayref}"
            )
            if arrayref.value == 0:
                output = "null pointer"
            else:
                array = state.heap.memory[arrayref.value - 1]
                assert isinstance(array, jvmc.HeapArray), (
                    f"expected HeapArray, but got {array}"
                )
                # Check for out of bounds
                if not (0 <= index.value and index.value < len(array.values)):
                    output = "out of bounds"
                else:
                    value = array.values[index.value]
                    frame.stack.push(jvmc.StackInt(value))
                    frame.pc += 1

        case jvm.InvokeVirtual(method=m):
            # Handle java.lang.String.equals
            if m.encode().startswith("java.lang.String.equals"):
                ref1, ref2 = frame.stack.pop(), frame.stack.pop()
                assert isinstance(ref1, jvmc.StackReference), (
                    f"expected ref1 to be StackReference, but got {ref1}"
                )
                assert isinstance(ref2, jvmc.StackReference), (
                    f"expected ref2 to be StackReference, but got {ref2}"
                )
                if ref1.value == 0 or ref2.value == 0:
                    output = "null pointer"
                else:
                    string1 = state.heap.memory[ref1.value - 1]
                    string2 = state.heap.memory[ref2.value - 1]
                    assert isinstance(string1, jvmc.HeapString), (
                        f"expected HeapString, but got {string1}"
                    )
                    assert isinstance(string2, jvmc.HeapString), (
                        f"expected HeapString, but got {string2}"
                    )
                    result = string1.content == string2.content
                    frame.stack.push(jvmc.StackInt(1 if result else 0))
                    frame.pc += 1
            else:
                raise NotImplementedError(opr.help())

        case jvm.InvokeStatic(method=abs_methodid):
            # Create a new frame for the method
            newframe: jvmc.Frame = jvmc.Frame.from_method(bc.getmethod(abs_methodid))
            # Push parameters from the current frame's stack to the new frame's locals
            # Stack: arg1, arg2, ..., argN (top of the stack is the last argument)
            numparams = len(abs_methodid.methodid.params)
            for i in range(numparams):
                newframe.locals[numparams - i - 1] = frame.stack.pop()
            # Push the new frame onto the call stack, to be the frame executed from in the next step
            state.frames.push(newframe)

        case jvm.Negate():
            value = frame.stack.pop()
            assert isinstance(value, jvmc.StackInt), (
                f"expected StackInt, but got {value}"
            )
            frame.stack.push(jvmc.StackInt(-value.value))
            frame.pc += 1

        case a:
            raise NotImplementedError(a.help())

    assert isinstance(output, (jvmc.State, str))

    return pc, output


def initial(bc: jpamb.Bytecode, methodid: jvm.AbsMethodID, input: jpamb.Input):
    frame = jvmc.Frame.from_method(bc.getmethod(methodid))
    state = jvmc.State(jvmc.Heap(), jvmc.CallStack.from_frames([frame]))
    for i, v in enumerate(input.values):
        # Convert arbitrary values into local values
        match v:
            case jpamb.case.Boolean(value):
                frame.locals[i] = jvmc.StackInt(1 if value else 0)
            case jpamb.case.Int(value):
                frame.locals[i] = jvmc.StackInt(value)
            case jpamb.case.Array(contains=type, values=values):
                match type:
                    case jvm.Char():
                        ref = state.heap.new(
                            jvmc.HeapArray(type, [ord(a) for a in values])
                        )
                    case jvm.Int():
                        ref = state.heap.new(jvmc.HeapArray(type, [a for a in values]))
                frame.locals[i] = ref
            case jpamb.case.String(value=value):
                ref = state.heap.new(jvmc.HeapString(value))
                frame.locals[i] = ref
            case a:
                raise NotImplementedError(
                    f"Do not know how to convert values of type {a!r} to a local value"
                )
    return state


def interpret():
    """The concolic intepreter.b"""

    methodid, input, max_steps = jpamb.getcase(
        "coverage",
        "1.0",
        "TODO", #TODO: Figure out a name
        ["dynamic", "python", "coverage-based"],
        for_science=True,
    )

    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    state = initial(bc, methodid, input)

    last = jpamb.emit_init(state)

    for _ in range(max_steps):
        pc, state = step(bc, state)
        last = jpamb.emit_step(last, pc, state)

        if isinstance(state, str):
            break


def fuzz_input(rand: random.Random, methodid: jvm.AbsMethodID) -> jpamb.case.Input:
    input = []
    # 1. come up with possible inputs
    for p in methodid.extension.params:
        match p:
            case jvm.Int():
                input.append(jpamb.case.Int(rand.randint(-(1 << 31), 1 << 31)))
            case jvm.Boolean():
                input.append(jpamb.case.Boolean(1 == rand.randint(0, 1)))
            case a:
                raise NotImplementedError(
                    "Don't know how to create random values for {input}"
                )

    return jpamb.case.Input(input)

def concolicAnalyse(pc : jvmc.PC, inputs : list[tuple[str, jvm.Type]], max_depth : int):
  # assuming only integers, create symbolic vars for all input
  locals = z3.Ints(" ".join(i_name for i_name, _ in inputs))
  # create state.
  state = SymState.from_locals(locals)

  # Create a stack to do depth first search with.
  stack : list[tuple[jvmc.PC, SymState, SymPath, int]] = [(pc, state, [],0)]

  # As long as the stack is not empty
  while stack:
    # pop the end of the stack
    (pc, state, path, n) = stack.pop(-1)

    # Check if state does something we want to warn the user about.
    if interesting(state):
      return "found interesting state"

    # otherwise create the list of next branches 
    for (pc, state_, pathc) in step(pc, state):
        # add new path constraints to the path
        path_ = path + pathc

        # check if path is reachable
        if str(z3.check(path_)) != "sat": 
          continue

        # append stack if within limits
        if n < max_depth:
          stack.append((pc, state_, path_, n + 1))

  return f"all is fine, uptil depth {max_depth}"


def analyse():
    """The concolic analysis, e.g. in this case a (dumb) fuzzer."""

    methodid = jpamb.getmethodid(
        "dynamic",
        "1.0",
        "Dynamo",
        ["dynamic", "python"],
        for_science=True,
    )

    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    MAX_STEPS = 10000

    import random

    # Make the randomness deterministic
    rand = random.Random(0)

    behaviors = set()
    # Try random inputs
    randomTries = 50
    for i in range(randomTries):
        input = fuzz_input(rand, methodid)
        

        # state = initial(bc, methodid, input)

        # for x in range(MAX_STEPS):
        #     _, state = step(bc, state)
        #     if isinstance(state, str):
        #         behaviors.add(state)
        #         break
        #     elif x == MAX_STEPS - 1:
        #         behaviors.add("*")

    for query in jpamb.QUERIES:
        if query in behaviors:
            if query == "*":
                print(f"{query};timeout")
            elif query == "assertion error":
                print(f"{query};assertion-error-found")
            elif query == "divide by zero":
                print(f"{query};divide-by-zero-found")
            elif query == "null pointer":
                print(f"{query};null-pointer-found")
            elif query == "ok":
                print(f"{query};ok")
            elif query == "out of bounds":
                print(f"{query};out-of-bounds-found")
            else:
                print(f"{query};found")
        else:
            if query == "*":
                print(f"{query};no-timeout")
            elif query == "assertion error":
                print(f"{query};no-assertion-error")
            elif query == "divide by zero":
                print(f"{query};no-divide-by-zero")
            elif query == "null pointer":
                print(f"{query};no-null-pointer")
            elif query == "ok":
                print(f"{query};no-ok")
            elif query == "out of bounds":
                print(f"{query};no-out-of-bounds")
            else:
                print(f"{query};found")

