import operator
import sys

class Solver:
    def __init__(self, clauses, variables):
        self.clauses = clauses
        self.vars = variables
        self.learnts = set()
        self.assigns = dict.fromkeys(list(self.vars), -1)
        self.step = 0
        self.nodes = self.set_initial_nodes()
        self.decision_var = {}
        self.implication_var = {}

    def solve(self):
        while self.have_unassigned():
            conf_cls = self.unit_propagate()
            if conf_cls is not None:
                st, learnt = self.conflict_analyze(conf_cls)
                if st < 0:
                    return False
                self.learnts.add(learnt)
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
        for v in [abs(lit) for lit in clause if abs(lit) != var]:
            self.nodes[v].children.append(node)
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
            if self.compute_clause(clause) == -1:
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

    def compute_clause(self, clause):
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

    def compute_value(self, var):
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
            if self.compute_value(clause[0]) == -1:
                return clause[0]
        for var in clause:
            value = self.compute_value(var)
            if value == 1:
                return None
            if value == -1:
                unassigned.append(var)
        if not len(unassigned) == 1:
            return None
        return unassigned[0]

    def get_propagation_conflict(self):
        prop = []
        all_clauses = list(self.clauses.union(self.learnts))
        for clause in all_clauses:
            val = self.compute_clause(clause)
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

    def conflict_analyze(self, conf_cls):

        def next_recent_assigned(clause):
            for v in reversed(assign_history):
                if v in clause or -v in clause:
                    return v, [x for x in clause if abs(x) != abs(v)]

        if self.step == 0:
            return -1, None

        assign_history = self.get_assign_history()

        pool_lits = conf_cls
        done_lits = set()
        curr_step_lits = set()
        prev_step_lits = set()

        while True:
            for lit in pool_lits:
                if self.nodes[abs(lit)].step == self.step:
                    curr_step_lits.add(lit)
                else:
                    prev_step_lits.add(lit)

            if len(curr_step_lits) == 1:
                break

            last_assigned, others = next_recent_assigned(curr_step_lits)

            done_lits.add(abs(last_assigned))
            curr_step_lits = set(others)

            pool_clause = self.nodes[abs(last_assigned)].clause
            pool_lits = []
            if pool_clause != None:
                for lit in pool_clause:
                    if not abs(lit) in done_lits:
                        pool_lits.append(lit)
        
        learnt = set()
        for var in curr_step_lits.union(prev_step_lits):
            learnt.add(var)
        learnt = frozenset(learnt)

        if prev_step_lits:
            step = max([self.nodes[abs(x)].step for x in prev_step_lits])
        else:
            step = self.step - 1
        return step, learnt

    def backtrack(self, to_step):
        self.remake_node(to_step)
        self.remake_record(to_step)
        
    def remake_node(self, to_step):    
        for var, node in self.nodes.items():
            if node.step <= to_step:
                node.children[:] = [child for child in node.children if child.step <= to_step]
            else:
                node.step = -1
                node.children = []
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
        self.children = []
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