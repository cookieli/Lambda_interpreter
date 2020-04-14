import random

PLUS  = ' + '
MINUS = ' - '
MUL   = ' * '
DIV   = ' / '
AND   = '&&'
OR    = '||'
LT    = '<'
GT    = '>'
EQ    = '='
symbol_map = {}
symbol_map[AND]   = lambda x,y: x and y
symbol_map[OR]    = lambda x,y: x or y
symbol_map[PLUS]  = lambda x,y: int(x + y)
symbol_map[MINUS] = lambda x,y: int(x - y)
symbol_map[MUL]   = lambda x,y: int(x * y)
symbol_map[DIV]   = lambda x,y: int(x // y)
symbol_map[LT]    = lambda x,y: x < y
symbol_map[GT]    = lambda x,y: x > y
symbol_map[EQ]    = lambda x,y: x == y

if_count = 0
unit_num_count = 0
if_bool_count = 0
unit_bool_count = 0
def gen_bool_value():
    choice = random.randint(1, 10000)
    mode = choice % 3
    if mode == 0:
        return "true", True
    elif mode == 1:
        return "false", False
    else :
        return gen_relop_expr()


def gen_unit_num():
    global unit_num_count
    unit_num_count +=1
    choice = random.randint(1, 100)
    module = 5
    if choice % module == 0:
        random.seed(choice)
        num = random.randint(-100, 100)
        return str(num), num
    else:
        random.seed(choice+1)
        num1 = random.randrange(-100, 100)
        num2 = random.randint(-100, 100)
        if choice % module == 1:
            return '(' + str(num1) + PLUS + str(num2) +')', num1 + num2
        elif choice % module == 2:
            return '(' + str(num1) + MINUS + str(num2) +')', num1 - num2
        elif choice % module == 3:
            return '(' + str(num1) + MUL + str(num2) +')', num1 * num2
        else:
            while num2 == 0:
                 num2 = random.randint(-100, 100)
            return '(' + str(num1) + DIV + str(num2) +')', num1 // num2

def get_string(name1, name2, symbol):
    return '(' + name1 + symbol + name2 + ')'

def gen_expr(symbols, unit_func):
    choice = random.randint(1, 10000)
    sym_len = len(symbols) + 1
    mode = choice % sym_len - 1
    if mode == -1:
        return unit_func()
    else:
        name1, value1 = unit_func()
        name2, value2 = unit_func()
        return get_string(name1, name2, symbols[mode]), symbol_map[symbols[mode]](value1, value2)


def gen_rand_expr(symbols, unit_func, connectors):
    count = random.randint(2, 2)
    expr, value = gen_expr(symbols, unit_func)
    conn_len = len(connectors)
    for _ in range(1, count):
        choice = random.randint(1, 10000)
        sub_expr, sub_value = gen_expr(symbols, unit_func)
        mode = choice % conn_len
        expr += connectors[mode] + sub_expr
        value = symbol_map[connectors[mode]](value, sub_value)

    return "(" + expr + ")", value

def gen_multi_expr(symbols, unit_func, connectors, concators):
    count = 2
    expr, value = gen_rand_expr(symbols, unit_func, connectors)
    for _ in range(1,count):
        sub_expr, sub_value = gen_rand_expr(symbols, unit_func, connectors)
        choice = random.randint(1, 10000)
        mode = choice % len(concators)
        expr += concators[mode] + sub_expr
        value = symbol_map[concators[mode]](value, sub_value)
    return expr, value

def gen_bool_expr():
    n = random.randint(0, 10000)
    global if_bool_count
    global unit_bool_count
    if (n % 2 == 0 and if_bool_count < 10) or (unit_bool_count - if_bool_count > 5 and if_bool_count < 5 ):
        return gen_if_bool_expr()
    unit_bool_count += 1
    return gen_multi_expr([AND,OR], gen_bool_value, [AND, OR],[AND, OR])

def gen_if_bool_expr():
    global if_bool_count
    if_bool_count += 1
    cond, value = gen_bool_expr()
    then, v_then = gen_bool_expr()
    else_, v_else = gen_bool_expr()
    ret = '(' + 'if' + ' ' + cond  + ' then ' + then + ' else ' + else_ + ')'
    if_value = v_then
    if not value:
        if_value = v_else
    return ret, if_value

def gen_if_num_expr():
    global if_count
    if_count += 1
    cond, c_value = gen_bool_expr()
    then_, v_then = gen_arith_expr()
    else_, v_else = gen_arith_expr()
    ret = '(' + 'if' + ' ' + cond  + ' then ' + then_ + ' else ' + else_ + ')'
    value = v_then
    if not c_value:
        value = v_else
    return ret, value 

def gen_random_num():
    global if_count 
    global unit_num_count

    num = random.randrange(0, 100000)
    if num % 2 == 0 and if_count < 20 or (unit_num_count - if_count > 5 and if_count <= 10):
        return gen_if_num_expr()
    else:
        return gen_unit_num()

def gen_arith_expr():
    arith_op = [PLUS, MINUS, MUL]
    return gen_multi_expr(arith_op, gen_random_num, arith_op, arith_op)

def gen_relop_expr():
    arith_op = [PLUS, MINUS, MUL]
    relops = [GT, LT, EQ]
    num1, value1 = gen_multi_expr(arith_op, gen_unit_num, arith_op, arith_op)
    num2, value2 = gen_multi_expr(arith_op, gen_unit_num, arith_op, arith_op)
    choice = random.randint(1, 10000)
    mode = choice % len(relops)
    return get_string(num1, num2, relops[mode]), symbol_map[relops[mode]](value1, value2)



if __name__ == '__main__':
    expr, value = gen_if_num_expr()
    print(expr)
    print(value)
    f = open("Correct_programs/if_07.lam", 'wb')
    f.write(expr.encode('utf-8'))
    f.close()
    f = open("Correct_programs/results/if_07.result", 'wb')
    if value:
        f.write('true'.encode('utf-8'))
    else:
        f.write('false'.encode('utf-8'))
    f.close()
