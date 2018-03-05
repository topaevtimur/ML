axioms = [
    "A -> (B -> A)",
    "(A -> B) -> (A -> B -> C) -> (A -> C)",
    "A -> B -> A & B",
    "A & B -> A",
    "A & B -> B",
    "A -> A | B",
    "A -> B | A",
    "(A -> B) -> (C -> B) -> (A | C -> B)",
    "(A -> B) -> (A -> !B) -> !A",
    "!!A -> A"
]

formal_axioms = [
    "a=b->a'=b'",
    "a=b->a=c->b=c",
    "a'=b'->a=b",
    "!(a'=0)",
    "a+b'=(a+b)'",
    "a+0=a",
    "a*0=0",
    "a*b'=a*b+a"
]
def addSpaces(string):
    result = ""
    i = 0
    while i < len(string):
        if string[i].isdigit() or string[i].isalpha():
            result += string[i]
            i += 1
        elif string[i] == "-":
            result += " -> "
            i += 2
        else:
            result += " " + string[i] + " "
            i += 1

    return result

mod = (10 ** 9) + 7

class Expression(object):
    hash = 0

    def __hash__(self):
        return self.hash

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

class Unary(Expression):
    def __init__(self, value):
        self.val = value

class Var(Unary):
    def __init__(self, value):
        self.hash = value.__hash__() % mod
        super().__init__(value)

    def __str__(self):
        return self.val

    def rehash(self):
        self.hash = self.val.__hash__()

    def eval(self, dictionary):
        return dictionary[self.val]

class Any(Unary):
    name = "@"

    def __init__(self, var, value):
        super().__init__(value)
        self.var = var
        self.rehash()

    def __str__(self):
        return "(@" + self.var.__str__() + self.val.__str__() + ")"

    def rehash(self):
        self.hash = (17 * self.var.__hash__() ** 3 + 3 * self.val.__hash__() ** 2 + 7 * self.name.__hash__()) % mod


class Not(Unary):
    name = "!"

    def __init__(self, value):
        super().__init__(value)
        self.rehash()

    def __str__(self):
        return "(!" + self.val.__str__() + ")"

    def rehash(self):
        self.hash = (3 * self.val.__hash__() ** 2 + 7 * self.name.__hash__()) % mod

    def eval(self, dictionary):
        return not self.val.eval(dictionary)

class Exists(Unary):
    name = "?"

    def __init__(self, var, value):
        super().__init__(value)
        self.var = var
        self.rehash()

    def __str__(self):
        return "(?" + self.var.__str__() + self.val.__str__() + ")"

    def rehash(self):
        self.hash = (17 * self.var.__hash__() ** 3 + 3 * self.val.__hash__() ** 2 + 7 * self.name.__hash__()) % mod


class Predicate(Unary):
    def __init__(self, name, values):
        self.name = name
        super().__init__(values)
        self.rehash()

    def __str__(self):
        if len(self.val) == 0:
            return self.name
        result = self.name + "("
        for i in range(len(self.val)):
            if i == len(self.val) - 1:
                result += self.val[i].__str__() + ")"
            else:
                result += self.val[i].__str__() + ","
        return result

    def rehash(self):
        self.hash = self.name.__hash__() % mod
        for e in self.val:
            self.hash *= 37
            self.hash += e.__hash__()


class Next(Unary):
    name = "'"

    def __init__(self, value):
        super().__init__(value)
        self.rehash()

    def __str__(self):
        return self.val.__str__() + self.name

    def rehash(self):
        self.hash = (self.val.__hash__() * 31 + self.name.__hash__()) % mod


class Binary(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.rehash()

    def __str__(self):
        return "(" + self.left.__str__() + self.name + self.right.__str__() + ")"

    def rehash(self):
        self.hash = (3 * self.name.__hash__() + 11 * self.left.__hash__()**3 + 23 * self.right.__hash__()**4) % mod

    def calc(self, left, right):
        raise NotImplementedError

    def eval(self, dictionary):
        return self.calc(self.left.eval(dictionary), self.right.eval(dictionary))


class Implication(Binary):
    name = "->"

    def __init__(self, left, right):
        super().__init__(left, right)

    def calc(self, left, right):
        return (not left) or right


class Conjuction(Binary):
    name = "&"

    def __init__(self, left, right):
        super().__init__(left, right)

    def calc(self, left, right):
        return left and right


class Disjuction(Binary):
    name = "|"

    def __init__(self, left, right):
        super().__init__(left, right)

    def calc(self, left, right):
        return left or right


class Equals(Binary):
    name = "="

    def __init__(self, left, right):
        super().__init__(left, right)


class Sum(Binary):
    name = "+"

    def __init__(self, left, right):
        super().__init__(left, right)


class Mul(Binary):
    name = "*"

    def __init__(self, left, right):
        super().__init__(left, right)


def match(exp, axiom, dictionary):
    if type(axiom) is Var:
        if axiom in dictionary:
            return dictionary[axiom] == exp
        else:
            dictionary[axiom] = exp
            return True
    elif type(exp) is type(axiom):
        if isinstance(axiom, Unary):
            return match(exp.val, axiom.val, dictionary)
        else:
            sub = match(exp.left, axiom.left, dictionary)
            if sub:
                sub = match(exp.right, axiom.right, dictionary)

            return sub
    else:
        return False


def is_axiom(exp, checking_axiom):
    return match(exp, checking_axiom, {})


def get_variables(exp, dictionary: dict):
    if type(exp) is Var:
        if exp.val not in dictionary:
            dictionary[exp.val] = len(dictionary)
    elif isinstance(exp, Unary):
        get_variables(exp.val, dictionary)
    else:
        get_variables(exp.left, dictionary)
        get_variables(exp.right, dictionary)


def get_free_variables(exp, dictionary: dict, result: set):
    if type(exp) is Var:
        if exp not in dictionary.keys():
            result.add(exp.val)
    elif type(exp) is Predicate:
        for e in exp.val:
            get_free_variables(e, dictionary, result)
    elif type(exp) is Any or type(exp) is Exists:
        if exp.var in dictionary.keys():
            dictionary[exp.var] += 1
        else:
            dictionary[exp.var] = 1
        get_free_variables(exp.val,dictionary, result)
        dictionary[exp.var] -= 1
        if dictionary[exp.var] == 0:
            dictionary.pop(exp.var)
    elif isinstance(exp, Unary):
        get_free_variables(exp.val, dictionary, result)
    else:
        get_free_variables(exp.left, dictionary, result)
        get_free_variables(exp.right, dictionary, result)
    return result


def new_match(template, exp, locked : set, dictionary):
    if type(template) is Var:
        if template in locked:
            return template == exp
        else:
            if template in dictionary:
                return dictionary[template] == exp
            else:
                dictionary[template] = exp
                return True
    elif type(template) is type(exp):
        if type(template) is Any or type(template) is Exists:
            locked.add(template.var)
            result = new_match(template.val, exp.val, locked, dictionary)
            locked.remove(template.var)
            return result
        elif type(template) is Predicate:
            if len(template.val) != len(exp.val):
                return False
            for i in range(template.val):
                if not new_match(template.val[i], exp.val[i], locked, dictionary):
                    return False
            return True
        elif isinstance(template, Unary):
            return new_match(template.val, exp.val, locked, dictionary)
        else:
            if not new_match(template.left, exp.left, locked, dictionary):
                return False
            return new_match(template.right, exp.right, locked, dictionary)
    else:
        return False


def is_tautology(exp):
    temp = dict()
    get_variables(exp, temp)
    dictionary = dict()
    for e in temp:
        dictionary[temp[e]] = e

    for bits in range(0, 2 ** len(dictionary)):
        temp = dict()
        for j in range(0, len(dictionary)):
            if bits & (2 ** j) == 0:
                temp[dictionary[j]] = False
            else:
                temp[dictionary[j]] = True

        if not exp.eval(temp):
            return temp

    return dict()


class FormalParser:
    def __init__(self):
        self.string = ""
        self.index = 0

    def parseExpr(self, string):
        self.index = 0
        self.string = string
        return self.__parseImplication()

    def parse(self):
        if self.index >= len(self.string):
            return None
        return self.__parseImplication()

    def __readVarName(self):
        j = self.index
        while j < len(self.string) and (
            self.string[j].isdigit() or (self.string[j].isalpha() and self.string[j].islower())):
            j += 1
        result = self.string[self.index:j]
        self.index = j
        return result

    def __readPredicateName(self):
        j = self.index
        if not (self.string[j].isalpha() and self.string[j].isupper()):
            return ""
        while j < len(self.string) and (
            self.string[j].isdigit() or (self.string[j].isalpha() and self.string[j].isupper())):
            j += 1
        result = self.string[self.index:j]
        self.index = j
        return result

    def __parseImplication(self):
        result = self.__parseDisjuction()
        if self.index < len(self.string) and self.string[self.index] == '-':
            self.index += 2
            tmp = self.__parseImplication()
            return Implication(result, tmp)
        else:
            return result

    def __parseDisjuction(self):
        result = self.__parseConjuction()
        while self.index < len(self.string) and self.string[self.index] == '|':
            self.index += 1
            tmp = self.__parseConjuction()
            result = Disjuction(result, tmp)
        return result

    def __parseConjuction(self):
        result = self.__parseUnary()
        while self.index < len(self.string) and self.string[self.index] == '&':
            self.index += 1
            tmp = self.__parseUnary()
            result = Conjuction(result, tmp)
        return result

    def __parseUnary(self):
        if self.string[self.index] == '!':
            self.index += 1
            tmp = self.__parseUnary()
            return Not(tmp)
        elif self.string[self.index] == '@' or self.string[self.index] == '?':
            symbol = self.string[self.index]
            self.index += 1
            word = self.__readVarName()
            tmp = self.__parseUnary()
            if symbol == '@':
                return Any(Var(word), tmp)
            else:
                return Exists(Var(word), tmp)

        result = self.__parsePredicate()
        if not (result is None):
            return result

        if self.index < len(self.string) and self.string[self.index] == '(':
            self.index += 1
            result = self.__parseImplication()
            self.index += 1
            return result

        temp = self.__readVarName()
        return Var(temp)

    def __parsePredicate(self):
        word = self.__readPredicateName()
        if word != "":
            args = self.__parseArguments()
            return Predicate(word, args)
        else:
            save = self.index
            result = self.__parseTerm()
            if self.index >= len(self.string) or self.string[self.index] != '=':
                self.index = save
                return None
            self.index += 1
            return Equals(result, self.__parseTerm())

    def __parseArguments(self):
        result = list()
        if self.index >= len(self.string) or self.string[self.index] != '(':
            return result
        self.index += 1
        result.append(self.__parseTerm())
        while self.index < len(self.string) and self.string[self.index] != ')':
            self.index += 1
            result.append(self.__parseTerm())
        self.index += 1
        return result

    def __parseTerm(self):
        result = self.__parseSum()
        while self.index < len(self.string) and self.string[self.index] == '+':
            self.index += 1
            tmp = self.__parseSum()
            result = Sum(result, tmp)

        return result

    def __parseSum(self):
        result = self.__parseMul()
        while self.index < len(self.string) and self.string[self.index] == '*':
            self.index += 1
            tmp = self.__parseMul()
            result = Mul(result, tmp)

        return result

    def __parseMul(self):
        result = None
        if self.index < len(self.string) and self.string[self.index] == '(':
            self.index += 1
            result = self.__parseTerm()
            self.index += 1
            return self.__parseNext(result)
        word = self.__readVarName()
        if self.index < len(self.string) and self.string[self.index] == '(':
            values = self.__parseArguments()
            result = Predicate(word, values)
        else:
            result = Var(word)
        return self.__parseNext(result)

    def __parseNext(self, val):
        while self.index < len(self.string) and self.string[self.index] == '\'':
            self.index += 1
            val = Next(val)
        return val


def parseImplication(seq):
    result, seq = parseDisjuction(seq)
    while len(seq) > 0 and seq[0] == "->":
        tmp, seq = parseImplication(seq[1:])
        result = Implication(result, tmp)
    return result, seq

def parseExp(string):
    string = addSpaces(string)
    array = string.split()
    result, seq = parseImplication(array)
    return result


def parseDisjuction(seq):
    result, seq = parseConjuction(seq)
    while len(seq) > 0 and seq[0] == "|":
        tmp, seq = parseConjuction(seq[1:])
        result = Disjuction(result, tmp)
    return result, seq


def parseConjuction(seq):
    result, seq = parseNot(seq)
    while len(seq) > 0 and seq[0] == "&":
        tmp, seq = parseNot(seq[1:])
        result = Conjuction(result, tmp)
    return result, seq


def parseNot(seq):
    if seq[0] == "!":
        result, seq = parseNot(seq[1:])
        result = Not(result)
    else:
        result, seq = parseUnary(seq)
    return result, seq


def parseUnary(seq):
    if seq[0] == "(":
        tmp, seq = parseImplication(seq[1:])
        return tmp, seq[1:]
    else:
        tmp = Var(seq[0])
        return tmp, seq[1:]

axiomsExp = [parseExp(string) for string in axioms]
expression_parser = FormalParser()
formalAxioms = [expression_parser.parseExpr(string) for string in formal_axioms]


def is_any_axiom(expr):
    for i in range(len(axiomsExp)):
        if is_axiom(expr, axiomsExp[i]):
            return True

    return False


def subtract(expr, values):
    if type(expr) is Var:
        return expr
    elif type(expr) is Predicate:
        if expr.name in values:
            return values[expr.name]
        for i in range(len(expr.val)):
            expr[i] = subtract(expr.val[i], values)
    elif isinstance(expr, Unary):
        expr.val = subtract(expr.val, values)
    else:
        expr.left = subtract(expr.left, values)
        expr.right = subtract(expr.right, values)

    if (type(expr) is Any or type(expr) is Exists) and expr.var.val == "x":
        expr.var = values["x"].val

    expr.rehash()
    return expr


def createExpr(parser : FormalParser, string, values):
    return subtract(parser.parseExpr(string), values)


def addProof(address, proof, values):
    fin = open(address, "r")
    while True:
        line = fin.readline().rstrip()
        if not line:
            break

        proof.append(createExpr(line, values))
    fin.close()


class Proof(object):
    def __init__(self, expr, values):
        self.expression = expr
        self.assumptions = values
        self.expressions = []

    def deduction(self):
        new_expressions = []
        for i in range(len(self.expressions)):
            if self.expressions[i] == self.assumptions[0]:
                sub = {"A": self.expressions[i]}
                addProof("Proofs/A_Implication_A.proof", new_expressions, sub)
                continue

            if self.expressions[i] in self.assumptions or is_any_axiom(self.expressions[i]):
                sub = {"A": self.expressions[i], "B": self.assumptions[0]}
                new_expressions.append(self.expressions[i])
                new_expressions.append(createExpr("A->B->A", sub))
                new_expressions.append(createExpr("B->A", sub))
                continue

            for j in range(i - 1, -1, -1):
                tmp = Implication(self.expressions[j], self.expressions[i])
                if tmp in self.expressions:
                    sub = {"A": self.assumptions[0], "B": self.expressions[j], "C": self.expressions[i], "D": tmp}
                    new_expressions.append(createExpr("(A->B)->(A->D)->(A->C)", sub))
                    new_expressions.append(createExpr("(A->D)->(A->C)", sub))
                    new_expressions.append(createExpr("A->C", sub))
                    break
        self.expression = Implication(self.assumptions[0], self.expression)
        self.assumptions.pop(0)
        self.expressions = new_expressions

    def merge(self, other):
        sub = {"A": self.assumptions[0], "B": other.assumptions[0], "C": self.expression}

        self.deduction()
        other.deduction()

        sub["D"] = self.expression
        sub["E"] = other.expression

        self.expressions.extend(other.expressions)
        self.expressions.append(createExpr("D->E->(A|B->C)", sub))
        self.expressions.append(createExpr("E->(A|B->C)", sub))
        self.expressions.append(createExpr("(A|B->C)", sub))

        addProof("Proofs/Aor!A.proof", self.expressions, sub)
        self.expressions.append(sub["C"])
        self.expression = sub["C"]

    def print(self, file_name):
        for i in range(len(self.assumptions)):
            if i == len(self.assumptions) - 1:
                print(self.assumptions[i], end=" ", file=file_name)
            else:
                print(self.assumptions[i], end=", ", file=file_name)
        print("|-", self.expression, end="\n", file=file_name)
        for i in range(len(self.expressions)):
            print(self.expressions[i], end="\n", file=file_name)


def createProof(expr, proof):
    if type(expr) is Var:
        if expr in proof.assumptions:
            proof.expressions.append(expr)
            return True
        else:
            proof.expressions.append(Not(expr))
            return False
    elif type(expr) is Not:
        A = createProof(expr.val, proof)
        sub = {"A": expr.val}
        if A:
            addProof("Proofs/From_A_To_!!A.proof", proof.expressions, sub)
        return not A
    else:
        A = createProof(expr.left, proof)
        B = createProof(expr.right, proof)
        address = "Proofs/"
        if type(expr) is Implication:
            address += "Implication/"
        elif type(expr) is Conjuction:
            address += "And/"
        else:
            address += "Or/"

        if A:
            if B:
                address += "A_B.proof"
            else:
                address += "A_nB.proof"
        else:
            if B:
                address += "nA_B.proof"
            else:
                address += "nA_nB.proof"

        sub = {"A": expr.left, "B": expr.right}
        addProof(address, proof.expressions, sub)

        if proof.expressions[-1] == expr:
            return True
        else:
            return False


def free_subtract(template, exp, var, locked: dict, dictionary):
    if type(template) is Var:
        if template != var:
            return template == exp
        if template.val in locked:
            return template == exp
        else:
            if template in dictionary:
                return dictionary[template] == exp
            else:
                tmp = set()
                get_free_variables(exp, dict(), tmp)
                if len(tmp.intersection(locked)) != 0:
                    return False
                dictionary[template] = exp
                return True
    elif type(template) is type(exp):
        if type(template) is Any or type(template) is Exists:
            if template.var.val not in locked:
                locked[template.var.val] = 1
            else:
                locked[template.var.val] += 1
            result = free_subtract(template.val, exp.val, var, locked, dictionary)
            locked[template.var.val] -= 1
            if locked[template.var.val] == 0:
                locked.pop(template.var.val, None)
            return result
        elif type(template) is Predicate:
            if len(template.val) != len(exp.val):
                return False
            for i in range(len(template.val)):
                if not free_subtract(template.val[i], exp.val[i], var, locked, dictionary):
                    return False
            return True
        elif isinstance(template, Unary):
            return free_subtract(template.val, exp.val, var, locked, dictionary)
        else:
            if not free_subtract(template.left, exp.left, var, locked, dictionary):
                return False
            return free_subtract(template.right, exp.right, var, locked, dictionary)
    else:
        return False


def is_axiom_any(expr):
    if type(expr) is not Implication or type(expr.left) is not Any:
        return False
    return free_subtract(expr.left.val, expr.right, expr.left.var, dict(), dict())


def is_axiom_exists(expr):
    if type(expr) is not Implication or type(expr.right) is not Exists:
        return False
    return free_subtract(expr.right.val, expr.left, expr.right.var, dict(), dict())


def is_any_formal_axiom(expr: object) -> object:
    for axiom in formalAxioms:
        if new_match(axiom, expr, set(), dict()):
            return True
    if is_axiom_any(expr) or is_axiom_exists(expr):
        return True
    return False





def solve():
    fin = open("proof2.in", "r")
    fout = open("proof2.out", "w")

    parser = FormalParser()
    line, main_expression = fin.readline().rstrip().split("|-")
    assumptions = set()
    parser.string = line
    free_variables = set()
    last_assumption = None
    while parser.index < len(parser.string):
        tmp = parser.parse()
        last_assumption = tmp
        assumptions.add(tmp)
        # get_free_variables(tmp, dict(), free_variables)
        if parser.index < len(parser.string) and parser.string[parser.index] == ',':
            parser.index += 1
    if len(assumptions) > 0:
        get_free_variables(last_assumption, dict(), free_variables)
    parser.index += 2
    main_expression = parser.parseExpr(main_expression)
    expressions = set()
    expression_list = list()
    prior = list()
    line_number = 0
    check = False

    while True:
        line_number += 1
        if line_number % 1000 == 0:
            print("Now", line_number, "line")
        error_string = "[Unprooved statement]"
        line = fin.readline().rstrip()
        if not line:
            break
        expression = parser.parseExpr(line)
        check = -1, None

        if is_any_axiom(expression) or is_any_formal_axiom(expression):
            check = 0, None

        if check[0] == -1:
            # 9 predicate axiom ?
            if type(expression) is Implication and type(expression.left) is Conjuction \
                    and type(expression.left.right) is Any and type(expression.left.right.val) is Implication:
                if expression.left.right.var.val in get_free_variables(expression.right, dict(), set()) \
                        and free_subtract(expression.right, expression.left.right.val.right, Var(expression.left.right.var), dict(), dict()) \
                        and free_subtract(expression.right, expression.left.left, Var(expression.left.right.var), dict(), dict()) \
                        and expression.right == expression.left.right.val.left:
                    check = 0, None

        if check[0] == -1 and expression in assumptions:
            check = 1, None

        if check[0] == -1:
            for j in range(len(expression_list)):
                if Implication(expression_list[len(expression_list) - j - 1], expression) in expressions:
                    check = 2, expression_list[len(expression_list) - j - 1]
                    break

        if check[0] == -1:
            if type(expression) is Implication and type(expression.right) is Any:
                tmp = Implication(expression.left, expression.right.val)
                if tmp in expressions:
                    if expression.right.var.val not in get_free_variables(expression.left, dict(), set()):
                        if expression.right.var.val not in free_variables:
                            check = 3, tmp
                        else:
                            error_string = "[It's impossible to alter the proof. Applying rules with the quator of universality, free var - " \
                                           + expression.right.var.__str__() + " from assumptions.]"
                    else:
                        error_string = "[Error of applying the inference rules to the quantifier of universality. Var " \
                                       + expression.right.var.__str__() + " in free.]"

        if check[0] == -1:
            if type(expression) is Implication and type(expression.left) is Exists:
                tmp = Implication(expression.left.val, expression.right)
                if tmp in expressions:
                    if expression.left.var.val not in get_free_variables(expression.right, dict(), set()):
                        if expression.left.var.val not in free_variables:
                            check = 4, tmp
                        else:
                            error_string = "[It's impossible to alter the proof. Applying rules with the quator of existence, free var - " \
                                           + expression.left.var.__str__() + " from assumptions.]"
                    else:
                        error_string = "[[Error of applying the inference rules to the quantifier of existence. Var - " \
                                       + expression.right.var.__str__() + "in free.]"

        if check[0] == -1:
            print("Output isn't correct")
            print("Output isn't correct, from formula", line_number, ":", error_string, "\n", line, end="\n", file=fout)
            break
        else:
            expressions.add(expression)
            expression_list.append(expression)
            prior.append(check)

    if check[0] != -1:
        print("Output is correct")
        semicolomn = 0

        for e in assumptions:
            if e != last_assumption:
                print(e, sep="", end="", file=fout)
                if semicolomn < len(assumptions) - 2:
                    print(",", sep="", end="", file=fout)
                semicolomn += 1

        if len(assumptions) > 0:
            print("|-", Implication(last_assumption, main_expression), sep="", end="\n", file=fout)
            fany = open("Proofs/any_rule.proof", "r")
            any_proof = fany.readlines()
            fany.close()
            fexists = open("Proofs/exists_rule.proof", "r")
            exists_proof = fexists.readlines()
            fexists.close()
            for i in range(len(expression_list)):
                if prior[i][0] == 0:
                    # axiom ?
                    print(Implication(expression_list[i], Implication(last_assumption, expression_list[i])), file=fout)
                    print(expression_list[i], file=fout)
                    print(Implication(last_assumption, expression_list[i]), file=fout)
                elif prior[i][0] == 1:
                    # assumption ?
                    if expression_list[i] != last_assumption:
                        print(Implication(expression_list[i], Implication(last_assumption, expression_list[i])), file=fout)
                        print(expression_list[i], file=fout)
                        print(Implication(last_assumption, expression_list[i]), file=fout)
                    else:
                        tmp1 = Implication(last_assumption, Implication(last_assumption, last_assumption))
                        print(tmp1, file=fout)

                        tmp2 = Implication(last_assumption, Implication(Implication(last_assumption, last_assumption), last_assumption))
                        tmp3 = Implication(last_assumption, last_assumption)
                        print(Implication(tmp1, Implication(tmp2, tmp3)), file=fout)
                        print(Implication(tmp2, tmp3), file=fout)
                        print(tmp2, file=fout)
                        print(tmp3, file=fout)
                elif prior[i][0] == 2:
                    # Modus Ponens ?
                    tmp = Implication(last_assumption, Implication(prior[i][1], expression_list[i]))
                    tmp1 = Implication(last_assumption, prior[i][1])
                    tmp2 = Implication(last_assumption, expression_list[i])
                    print(Implication(tmp1, Implication(tmp, tmp2)), file=fout)
                    print(Implication(tmp, tmp2), file=fout)
                    print(tmp2, file=fout)
                elif prior[i][0] == 3:
                    # Any ?
                    mapping = {"A" : last_assumption, "B" : expression_list[i].left, "C" : expression_list[i].right.val, "x" : expression_list[i].right.var}
                    for i in range(len(any_proof)):
                        str = any_proof[i]
                        tempExpr = createExpr(parser, str.rstrip(), mapping)
                        print(tempExpr, file=fout)
                elif prior[i][0] == 4:
                    # Exists ?
                    mapping = {"A" : last_assumption, "B" : expression_list[i].left.val, "C" : expression_list[i].right, "x" : expression_list[i].left.var}
                    for str in exists_proof:
                        print(createExpr(parser, str, mapping), file=fout)
        else:
            print("|-", main_expression, sep="", file=fout)
            for expr in expression_list:
                print(expr, file=fout)

    fin.close()
    fout.close()

solve()
