import operator
import sys

class Solver:
    def __init__(self, clauses, variables):
        self.clauses = clauses
        self.vars = variables
        self.learned_clauses = set()
        self.assigns = dict.fromkeys(list(self.vars), -1)
        self.step = 0
        self.nodes = self.set_initial_nodes()
        self.decision_var = {}
        self.implication_var = {}

    def solve(self):
        while self.have_unassigned():
            conf_clause = self.unit_propagate()
            if conf_clause is not None:
                st, learned = self.conflict_analyze(conf_clause)
                if st < 0:
                    return False
                self.learned_clauses.add(learned)
                self.backtrack(st)
                self.step = st
            elif not self.have_unassigned():
                break
            else:
                self.step += 1
                var, val = self.decide_variable()
                self.assigns[var] = val
                self.decision_var[self.step] = var
                self.implication_var[self.step] = []
                self.set_node(var)
        return True

    def set_initial_nodes(self):
        nodes = {}
        for var in list(self.vars):
            node = Node(var)
            nodes[var] = node
        return nodes

    def set_node(self, var):
        node = self.nodes[var]
        node.step = self.step

    def update_implication(self, var, clause):
        self.set_node(var)
        node = self.nodes[var]
        node.clause = clause

    def all_unassigned_vars(self):
        res = set()
        for v in self.assigns.keys():
            if self.assigns[v] == -1:
                res.add(v)
        return list(res)
    
    def all_unresolved_clauses(self):
        res = []
        for clause in self.clauses:
            if self.get_value_from_clause(clause) == -1:
                res.append(clause)
        return res

    def decide_variable(self):
        def make_tuple(x):
            return (x, 0)
        unassigned = self.all_unassigned_vars()
        pos = dict(list(map(make_tuple, unassigned)))
        neg = dict(list(map(make_tuple, unassigned)))
        for clause in self.all_unresolved_clauses():
            for v in clause:
                if v in pos.keys():
                    if v > 0:
                        pos[v] += 1
                    else:
                        neg[abs(v)] += 1
                else:
                    pass
        pos_count = max(pos.items(), key = operator.itemgetter(1))
        neg_count = max(neg.items(), key = operator.itemgetter(1))
        if pos_count[1] > neg_count[1]:
            return pos_count[0], 1
        else:
            return neg_count[0], 0

    def have_unassigned(self):
        for var in self.vars:
            if not var in self.assigns:
                return True
        for var in self.vars:
            if self.assigns[var] == -1:
                return True
        return False

    def get_value_from_clause(self, clause):
        values = []
        for var in clause:
            value = self.assigns[abs(var)]
            if value == -1:
                values.append(-1)
            else:
                if var < 0:
                    if value == 1:
                        values.append(0)
                    else:
                        values.append(1)
                else:
                    if value == 0:
                        values.append(0)
                    else:
                        values.append(1)
        if -1 in values:
            return -1
        else:
            return max(values)

    def get_value_from_var(self, var):
        value = self.assigns[abs(var)]
        if value == -1:
            return -1
        else:
            if var < 0:
                if value == 1:
                    return 0
                else:
                    return 1
            else:
                if value == 1:
                    return 1
                else:
                    return 0

    def get_unit_literal(self, clause):
        unassigned = []
        if len(clause) == 1:
            clause = list(clause)
            if self.get_value_from_var(clause[0]) == -1:
                return clause[0]
        for var in clause:
            value = self.get_value_from_var(var)
            if value == 1:
                return None
            if value == -1:
                unassigned.append(var)
        if not len(unassigned) == 1:
            return None
        return unassigned[0]

    def get_propagation_conflict(self):
        prop = []
        all_clauses = list(self.clauses.union(self.learned_clauses))
        for clause in all_clauses:
            val = self.get_value_from_clause(clause)
            if val == 1:
                continue
            if val == 0:
                return prop, clause
            else:
                unit_literal = self.get_unit_literal(clause)
                if unit_literal == None:
                    continue
                prop_pair = (unit_literal, clause)
                if prop_pair not in prop:
                    prop.append(prop_pair)
        return prop, None

    def unit_propagate(self):
        while True:
            prop, conflict = self.get_propagation_conflict()
            if conflict != None:
                return conflict
            if prop == []:
                return None
            for prop_literal, clause in prop:
                prop_var = abs(prop_literal)
                if prop_literal > 0:
                    self.assigns[prop_var] = 1
                else:
                    self.assigns[prop_var] = 0
                self.update_implication(prop_var, clause)
                if self.step in self.implication_var.keys():
                    self.implication_var[self.step].append(prop_literal)
    
    def get_assign_history(self):
        return [self.decision_var[self.step]] + self.implication_var[self.step]

    def learn_from_conflict(self, assign, conflict_clause):
        todo = conflict_clause
        done = set()
        curr = set()
        prev = set()
        while True:
            for lit in todo:
                if self.nodes[abs(lit)].step == self.step:
                    curr.add(lit)
                else:
                    prev.add(lit)

            if len(curr) == 1:
                break
            
            for v in reversed(assign):
                if v in curr or -v in curr:
                    last_assigned = v
                    others = []
                    for l in curr:
                        if abs(l) != abs(v):
                            others.append(l)
                    break

            done.add(abs(last_assigned))
            curr = set(others)

            todo_clause = self.nodes[abs(last_assigned)].clause
            todo = []
            if todo_clause != None:
                for lit in todo_clause:
                    if not abs(lit) in done:
                        todo.append(lit)
        return self.learned_clause(curr.union(prev)), prev
    
    def learned_clause(self, clause):
        learned = set()
        for var in clause:
            learned.add(var)
        return frozenset(learned)

    def conflict_analyze(self, conflict_clause):
        if self.step == 0:
            return -1, None
        assign = self.get_assign_history()
        learned, prev = self.learn_from_conflict(assign, conflict_clause)

        if len(prev) != 0:
            step = max([self.nodes[abs(x)].step for x in prev])
        else:
            step = self.step - 1
        return step, learned

    def backtrack(self, to_step):
        self.remake_node(to_step)
        self.remake_record(to_step)
        
    def remake_node(self, to_step):    
        for var, node in self.nodes.items():
            if not node.step <= to_step:
                node.step = -1
                node.clause = None
                self.assigns[node.variable] = -1

    def remake_record(self, to_step):
        steps = list(self.implication_var.keys())
        for st in steps:
            if st <= to_step:
                continue
            del self.decision_var[st]
            del self.implication_var[st]

class Node:
    def __init__(self, var):
        self.variable = var
        self.step = -1
        self.clause = None

def make_result(filename):
    f = open(filename)
    info = []
    for line in f.readlines():
        if (not (line.startswith('c') or line.startswith('%') or line.startswith('0'))) and line != '\n':
            info.append(line.strip().split())
    variables = set()
    clauses = set()
    for line in info[1:]:
        clause = frozenset(map(int, line[:-1]))
        variables.update(map(abs, clause))
        clauses.add(clause)

    s = Solver(clauses, variables)

    if s.solve():
        print("s SATISFIABLE")
        res = ""
        prefix = "v"
        st = ""
        count = 0
        value = s.assigns.items()
        for var, val in value:
            if count == 0:
                st = st + prefix
            if val == 0:
                v = -var
                st = st + " " + str(v)
            else:
                st = st + " " + str(var)
            count += 1
            if count == 5:
                res = res + st + " 0\n"
                st = ""
                count = 0
        if st != "":
            res = res + st + " 0"
        print(res)
    else:
        print("s UNSATISFIABLE")

if __name__ == "__main__":
    filename = sys.argv[1]
    make_result(filename)