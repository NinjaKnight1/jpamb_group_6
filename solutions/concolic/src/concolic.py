import random
import sys
from dataclasses import dataclass

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

SymValue = z3.ArithRef
SymPath = tuple[z3.BoolRef, ...]


@dataclass
class SymFrame:
    method: jvm.AbsMethodID
    pc: jvmc.PC
    locals: list[SymValue | None]
    stack: list[SymValue]

    def clone(self) -> "SymFrame":
        return SymFrame(self.method, self.pc, self.locals.copy(), self.stack.copy())


@dataclass
class SymState:
    frames: list[SymFrame]
    result: str | None = None

    @classmethod
    def from_locals(
        cls,
        bc: jpamb.Bytecode,
        methodid: jvm.AbsMethodID,
        locals: list[SymValue],
    ) -> "SymState":
        method = bc.getmethod(methodid)
        if len(locals) > method.max_locals:
            raise ValueError("More symbolic inputs than method local variables")
        frame_locals: list[SymValue | None] = [None] * method.max_locals
        frame_locals[: len(locals)] = locals
        frame = SymFrame(methodid, jvmc.PC(methodid, 0), frame_locals, [])
        return cls([frame])

    @property
    def frame(self) -> SymFrame:
        return self.frames[-1]

    def clone(self) -> "SymState":
        return SymState([frame.clone() for frame in self.frames], self.result)


def interesting(state: SymState) -> bool:
    """A completed JVM behavior is an outcome worth reporting."""
    return state.result is not None


def _wrap_int(value: SymValue) -> SymValue:
    """Wrap an integer expression to the JVM's signed 32-bit range."""
    return (value + (1 << 31)) % (1 << 32) - (1 << 31)


def _java_divide(left: SymValue, right: SymValue) -> SymValue:
    left_abs = z3.If(left >= 0, left, -left)
    right_abs = z3.If(right >= 0, right, -right)
    quotient = left_abs / right_abs
    return z3.If((left < 0) != (right < 0), -quotient, quotient)


def _symbolic_compare(
    condition: jvm.CmpOpr, left: SymValue, right: SymValue
) -> z3.BoolRef:
    match condition:
        case jvm.CmpOpr.Eq:
            return left == right
        case jvm.CmpOpr.Ne:
            return left != right
        case jvm.CmpOpr.Gt:
            return left > right
        case jvm.CmpOpr.Ge:
            return left >= right
        case jvm.CmpOpr.Lt:
            return left < right
        case jvm.CmpOpr.Le:
            return left <= right
        case _:
            raise NotImplementedError(f"Unhandled comparison {condition!r}")


def _satisfiable(path: SymPath) -> bool:
    solver = z3.Solver()
    solver.add(*path)
    result = solver.check()
    if result == z3.unknown:
        raise RuntimeError(f"Z3 could not decide path reachability: {solver.reason_unknown()}")
    return result == z3.sat


def _symbolic_step(
    bc: jpamb.Bytecode, state: SymState, path: SymPath
) -> list[tuple[SymState, SymPath]]:
    frame = state.frame
    pc = frame.pc
    opr = bc[pc]

    def pop() -> SymValue:
        if not frame.stack:
            raise IndexError(f"Operand stack underflow at {pc}")
        return frame.stack.pop()

    def advance() -> None:
        frame.pc += 1

    match opr:
        case jvm.Push(type=jvm.Int(), value=value):
            assert isinstance(value, int)
            frame.stack.append(z3.IntVal(value))
            advance()
        case jvm.Binary(type=jvm.Int(), operant=operation):
            right, left = pop(), pop()
            if operation in (jvm.BinaryOpr.Div, jvm.BinaryOpr.Rem):
                zero = right == 0
                error = state.clone()
                error.result = "divide by zero"
                normal = state.clone()
                normal.frame.stack.append(
                    _wrap_int(
                        _java_divide(left, right)
                        if operation == jvm.BinaryOpr.Div
                        else left - _java_divide(left, right) * right
                    )
                )
                normal.frame.pc += 1
                return [
                    (error, path + (zero,)),
                    (normal, path + (z3.Not(zero),)),
                ]

            match operation:
                case jvm.BinaryOpr.Add:
                    value = left + right
                case jvm.BinaryOpr.Sub:
                    value = left - right
                case jvm.BinaryOpr.Mul:
                    value = left * right
                case _:
                    raise NotImplementedError(f"Unhandled binary operation {operation!r}")
            frame.stack.append(_wrap_int(value))
            advance()
        case jvm.Ifz(condition=condition, target=target):
            value = pop()
            predicate = _symbolic_compare(condition, value, z3.IntVal(0))
            taken, fallthrough = state.clone(), state.clone()
            taken.frame.pc %= target
            fallthrough.frame.pc += 1
            return [
                (taken, path + (predicate,)),
                (fallthrough, path + (z3.Not(predicate),)),
            ]
        case jvm.If(condition=condition, target=target):
            right, left = pop(), pop()
            predicate = _symbolic_compare(condition, left, right)
            taken, fallthrough = state.clone(), state.clone()
            taken.frame.pc %= target
            fallthrough.frame.pc += 1
            return [
                (taken, path + (predicate,)),
                (fallthrough, path + (z3.Not(predicate),)),
            ]
        case jvm.Load(type=jvm.Int(), index=index):
            value = frame.locals[index]
            if value is None:
                raise IndexError(f"Read of uninitialized local {index} at {pc}")
            frame.stack.append(value)
            advance()
        case jvm.Store(type=jvm.Int(), index=index):
            frame.locals[index] = pop()
            advance()
        case jvm.Incr(index=index, amount=amount):
            value = frame.locals[index]
            if value is None:
                raise IndexError(f"Read of uninitialized local {index} at {pc}")
            frame.locals[index] = _wrap_int(value + amount)
            advance()
        case jvm.Dup(words=1):
            value = pop()
            frame.stack.extend((value, value))
            advance()
        case jvm.Goto(target=target):
            frame.pc %= target
        case jvm.Cast(from_=jvm.Int(), to_=jvm.Short()):
            frame.stack.append(pop() % (1 << 16))
            advance()
        case jvm.Negate(type=jvm.Int()):
            frame.stack.append(_wrap_int(-pop()))
            advance()
        case jvm.Get(static=True, field=field):
            if field.extension.name != "$assertionsDisabled":
                raise NotImplementedError(f"Unhandled static field {field}")
            frame.stack.append(z3.IntVal(0))
            advance()
        case jvm.New(classname=jvm.ClassName("java.lang.AssertionError")):
            state.result = "assertion error"
        case jvm.Return(type=return_type):
            value = pop() if isinstance(return_type, jvm.Int) else None
            state.frames.pop()
            if not state.frames:
                state.result = "ok"
            else:
                caller = state.frame
                if value is not None:
                    caller.stack.append(value)
                caller.pc += 1
        case jvm.InvokeStatic(method=methodid):
            callee_method = bc.getmethod(methodid)
            parameter_count = len(methodid.extension.params)
            arguments = [pop() for _ in range(parameter_count)]
            arguments.reverse()
            if parameter_count > callee_method.max_locals:
                raise ValueError(f"Too many arguments for {methodid}")
            callee_locals: list[SymValue | None] = [None] * callee_method.max_locals
            callee_locals[:parameter_count] = arguments
            state.frames.append(
                SymFrame(methodid, jvmc.PC(methodid, 0), callee_locals, [])
            )
        case _:
            raise NotImplementedError(
                f"Symbolic execution does not support {opr!r} at {pc}"
            )

    return [(state, path)]


def concolicAnalyse(
    bc: jpamb.Bytecode,
    methodid: jvm.AbsMethodID,
    inputs: list[tuple[str, jvm.Type]],
    max_depth: int,
) -> set[str]:
    """Explore feasible integer-input paths up to ``max_depth`` instructions."""
    if max_depth < 0:
        raise ValueError("max_depth must be non-negative")

    symbolic_inputs: list[SymValue] = []
    initial_path: SymPath = ()
    for index, (name, input_type) in enumerate(inputs):
        if isinstance(input_type, jvm.Int):
            value = z3.Int(f"{name}_{index}")
            initial_path += (value >= -(1 << 31), value < (1 << 31))
        elif isinstance(input_type, jvm.Boolean):
            value = z3.Int(f"{name}_{index}")
            initial_path += (value >= 0, value <= 1)
        else:
            raise NotImplementedError(
                f"Symbolic inputs of type {input_type} are not supported"
            )
        symbolic_inputs.append(value)

    initial_state = SymState.from_locals(bc, methodid, symbolic_inputs)
    worklist: list[tuple[SymState, SymPath, int]] = [
        (initial_state, initial_path, 0)
    ]
    behaviors: set[str] = set()

    while worklist:
        state, path, depth = worklist.pop()
        if interesting(state):
            assert state.result is not None
            behaviors.add(state.result)
            continue
        if depth >= max_depth:
            behaviors.add("*")
            continue

        for next_state, next_path in _symbolic_step(bc, state, path):
            if _satisfiable(next_path):
                worklist.append((next_state, next_path, depth + 1))

    return behaviors


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
    behaviors = set()
    inputs = [
        (f"arg{index}", input_type)
        for index, input_type in enumerate(methodid.extension.params)
    ]
    behaviors.update(concolicAnalyse(bc, methodid, inputs, MAX_STEPS))

    # print answers
    printAnswer(behaviors)


def printAnswer(behaviors: set[str]):
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

