'''
Created on 11 Nov 2010

@author: itsbth
'''
import ast, _ast
import re
import linecache

_LOCAL_RE = re.compile(r'@(?P<id>[A-Za-z0-9_]+)')

_BINOP = {
    _ast.Add: 'add',
    _ast.Sub: 'sub',
    _ast.Mult: 'mul',
    _ast.Div: 'div',
    #_ast.FloorDiv: operator.floordiv,
    _ast.Mod: 'mod',
    #_ast.Pow: operator.pow,
    _ast.LShift: '<<',
    _ast.RShift: '>>',
    _ast.BitOr: '|',
    _ast.BitXor: '^',
    _ast.BitAnd: '&'
}

_COMP = {
    _ast.Eq: 'jeq',
    _ast.NotEq: 'jne',
    _ast.Gt: 'jg',
    _ast.GtE: 'jge',
    _ast.Lt: 'jl',
    _ast.LtE: 'jle',
}

CONSTANT_NUM = 1
CONSTANT_STR = 2

def _getconstant(expr):
    typ = type(expr)
    if typ == _ast.Num:
        return (CONSTANT_NUM, expr.n)
    if typ == _ast.Str:
        return (CONSTANT_STR, expr.s)
    raise UncompatibleCodeException, 'is not a constant'

def _compilecall(parent, call):
    buff = []
    name = call.func.id
    for arg in reversed(call.args):
        comp = ExpressionCompiler(parent, arg)
        buff.append(comp.run())
        buff.append("push eax;\n")
    buff.append("call _%s;\n" % name)
    buff.append("add esp,%d;\n" % len(call.args))
    return ''.join(buff)

class UncompatibleCodeException(Exception): pass

class ExpressionCompiler(object):
    def __init__(self, parent, expr, tmp_id=0):
        self.parent = parent
        self.root = parent.parent
        self.expr = expr
        self.buffer = []
        self.tmp_id = tmp_id
    
    def run(self, to='eax'):
        self.buffer.append("mov ecx,__expr__tmp__;\n")
        self._run(self.expr, to=to)
        return ''.join(self.buffer)
    
    def _run(self, expr, to='eax'):
        typ = type(expr)
        if typ == _ast.Expr:
            self._run(expr, to=to)
        elif typ == _ast.Num:
            self.buffer.append("mov %s,%d;\n" % (to, expr.n))
        elif typ == _ast.Str:
            self.buffer.append("mov %s,%s;\n" % (to, self.root. _getstring(expr.s)))
        elif typ == _ast.BinOp:
            self._binop(expr, to=to)
        elif typ == _ast.Compare:
            self._compare(expr, to=to)
        elif typ == _ast.Name:
            self._name(expr, to=to) 
        elif typ == _ast.Subscript:
            self._subscript(expr, to=to)
        elif typ == _ast.Call:
            self.buffer.append(_compilecall(self.parent, expr))
    
    def _binop(self, expr, to='eax'):
        self._run(expr.left, to=to)
        self.tmp_id += 1
        self._run(expr.right, to='ecx:#%d' % self.tmp_id)
        self.buffer.append("%s %s,ecx:#%d;\n" % (_BINOP[type(expr.op)], to, self.tmp_id))
        self.tmp_id -= 1
    
    def _compare(self, expr, to='eax'):
        label = self.parent._genid()
        self.buffer.append("mov %s,1;\n" % to)
        self.tmp_id += 1
        self._run(expr.left, to='ecx:#%d' % self.tmp_id)
        self.tmp_id += 1
        self._run(expr.comparators[0], to='ecx:#%d' % self.tmp_id)
        self.buffer.append("cmp ecx:#%d,ecx:#%d;\n" % (self.tmp_id - 1, self.tmp_id))
        self.buffer.append("%s %s;\n" % (_COMP[type(expr.ops[0])], label))
        self.buffer.append("mov %s,0;\n" % to)
        self.buffer.append("%s:\n" % label)
        self.tmp_id -= 2
    
    def _name(self, expr, to='eax'):
        name = expr.id
        aname = None
        if name in self.parent.locals:
            aname = "esp:#%d" % self.parent.locals[name]
        else:
            aname = "#_%s" % name
        self.buffer.append("mov %s,%s;\n" %(to, aname))
    
    def _subscript(self, sub, to):
        comp = ExpressionCompiler(self.parent, sub.slice.value, tmp_id=self.tmp_id)
        self.buffer.append(comp.run(to='ebx'))
        self.parent._assignable(sub.value, to=to)
        self.buffer.append("add %s,ebx;\n" % to)
        self.buffer.append("mov %s,%s;\n" % (to, to))

class FunctionCompiler(object):
    def __init__(self, parent, func):
        self.parent = parent
        self.func = func
        self.buffer = []
        self.locals = {} # name => pos
        self.arguments = {}
        i = -1
        for arg in func.args.args:
            self.arguments[arg.id] = i
            i -= 1
        self.lid = 0 
        self.nid = 0
        
    def run(self):
        buff = []
        buff.append("_%s:\n" % self.func.name)
        for stmnt in self.func.body:
            self._compilestatement(stmnt)
        buff.append("sub esp,%d;\n" % self.lid)
        buff.append(''.join(self.buffer))
        buff.append("add esp,%d;\n" % self.lid)
        buff.append("ret;\n")
        return ''.join(buff)
    
    def _genid(self):
        self.nid += 1
        return "__%s__%d__" % (self.func.name, self.nid)
    
    def _local(self, name):
        if name in self.arguments:
            return self.arguments[name]
        if name in self.locals:
            return self.locals[name]
        else:
            self.locals[name] = self.lid
            self.lid += 1
            return self.locals[name]
    
    def _assignable(self, target, to='ecx'):
        if type(target) == _ast.Name:
            name = target.id
            if name in self.parent.globals:
                self.buffer.append("mov %s,_%s;\n" % (to, name))
            else:
                self.buffer.append("mov %s,esp:#%d;\n" % (to, self._local(name)))
        elif type(target) == _ast.Subscript:
            comp = ExpressionCompiler(self, target.slice.value)
            self.buffer.append(comp.run(to='ebx'))
            self._assignable(target.value, to=to)
            self.buffer.append("add %s,ebx;\n" % to)
    
    def _compilestatement(self, stmnt):
        self.buffer.append("//%s\n" % linecache.getline("test.py", stmnt.lineno).strip())
        typ = type(stmnt)
        if typ == _ast.While:
            self._compilewhile(stmnt)
        elif typ == _ast.If:
            self._compileif(stmnt)
        elif typ == _ast.Assign:
            if len(stmnt.targets) > 1:
                raise UncompatibleCodeException, 'only one target per assignment'
            target = stmnt.targets[0]
            comp = ExpressionCompiler(self, stmnt.value)
            self.buffer.append(comp.run())
            self._assignable(target, to='ecx')
            self.buffer.append("mov #ecx,eax;\n")
        elif typ == _ast.Return:
            comp = ExpressionCompiler(self, stmnt.value)
            self.buffer.append(comp.run())
        elif typ == _ast.Expr and type(stmnt.value) == _ast.Str:
            asm = _LOCAL_RE.sub(lambda m: "esp:#%d" % self._local(m.group('id')), stmnt.value.s)
            self.buffer.append("%s\n" % asm)
        elif typ == _ast.Expr and type(stmnt.value) == _ast.Call:
            self.buffer.append(_compilecall(self, stmnt.value))
        else:
            print typ
        
    def _compilewhile(self, stmnt):
        label = self._genid()
        label_end = "%send__" % label
        self.buffer.append("%s:\n" % label)
        comp = ExpressionCompiler(self, stmnt.test)
        self.buffer.append(comp.run())
        self.buffer.append("cmp eax,0;\n")
        self.buffer.append("jz %s;\n" % label_end)
        for item in stmnt.body:
            self._compilestatement(item)
        self.buffer.append("jmp %s;\n" % label)
        self.buffer.append("%s:\n" % label_end)
        
    def _compileif(self, stmnt):
        label = self._genid()
        label_end = "%send__" % label
        comp = ExpressionCompiler(self, stmnt.test)
        self.buffer.append(comp.run())
        self.buffer.append("cmp eax,0;\n")
        self.buffer.append("jz %s;\n" % label_end)
        for item in stmnt.body:
            self._compilestatement(item)
        self.buffer.append("%s:\n" % label_end)
    
class Compiler(object):
    '''
    classdocs
    '''

    def __init__(self, code, **kwargs):
        '''
        Constructor
        '''
        self.body = ast.parse(code).body
        self.functions = {}
        self.buffer = []
        self.globals = []
        self.constants = {}
        self.functions = {}
        self.strings = {}
        self.str_id = 0
    
    def _getstring(self, string):
        if string in self.strings:
            return self.strings[string]
        name = "_str_%d" % self.str_id
        self.str_id += 1
        self.strings[string] = name
        return name
    
    def parsefile(self):
        for stmnt in self.body:
            typ = type(stmnt)
            if typ == _ast.FunctionDef:
                self.parsefunction(stmnt)
            elif typ == _ast.Assign:
                self.parseglobal(stmnt)
            else:
                raise UncompatibleCodeException, "unable to compile '%s'" % typ 
    
    def parsefunction(self, func):
        comp = FunctionCompiler(self, func)
        self.buffer.append(comp.run())
    
    def parseglobal(self, glob):
        if len(glob.targets) > 1:
            raise UncompatibleCodeException, 'only one target per assignment'
        elif type(glob.targets[0]) != _ast.Name:
            raise UncompatibleCodeException, 'malformed global declaration'
        name, (typ, value) = glob.targets[0].id, _getconstant(glob.value)
        if typ == CONSTANT_NUM:
            self.numglobals[name] = value
        else:
            self.strglobals[name] = value
    
    def generate(self):
        buff = []
        buff.append("call _main;\n")
        buff.append(''.join(self.buffer))
        for k, v in self.strings.items():
            buff.append("%s: db '%s',0;\n" % (v, k.encode('string_escape')))
        buff.append("__expr__tmp__:\nalloc 128;\n")
        return ''.join(buff)
        
if __name__ == '__main__':
    comp = None
    with open('test.py') as file:
        comp = Compiler(file.read())
    comp.parsefile()
    print comp.generate()