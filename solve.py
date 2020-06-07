import operator

class Solver:

    def __init__(self, filename):
        self.clauses, self.vars = self.read_file(filename)
        self.learnts = set()
        self.assigns = dict.fromkeys(list(self.vars), -1)
        self.level = 0
        self.nodes = self.set_initial_nodes()
        self.branching_history = {}  # level -> branched variable
        self.propagate_history = {}  # level -> propagate variables list
    
    def set_initial_nodes(self):
        nodes = {}
        for var in list(self.vars):
            node = Node(var)
            nodes[var] = node
        return nodes

    def read_file(self, filename):
        with open(filename) as f:
            lines = [
                line.strip().split() for line in f.readlines()
                if (not (line.startswith('c') or
                         line.startswith('%') or
                         line.startswith('0'))
                    and line != '\n')
            ]

        literals = set()
        clauses = set()

        for line in lines[1:]:
            clause = frozenset(map(int, line[:-1]))
            literals.update(map(abs, clause))
            clauses.add(clause)

        return clauses, literals

    def solve(self):
        while self.have_unassigned():
            conf_cls = self.unit_propagate()
            if conf_cls is not None:
                lvl, learnt = self.conflict_analyze(conf_cls)
                if lvl < 0:
                    return False
                self.learnts.add(learnt)
                self.backtrack(lvl)
                self.level = lvl
            elif not self.have_unassigned():
                break
            else:
                self.level += 1
                bt_var, bt_val = self.pick_branching_variable()
                self.assigns[bt_var] = bt_val
                self.branching_history[self.level] = bt_var
                self.propagate_history[self.level] = []
                self.set_node(bt_var)
        return True

    def set_node(self, var):
        node = self.nodes[var]
        node.value = self.assigns[var]
        node.level = self.level

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
                res.update(v)
        return list(res)

    def all_unresolved_clauses(self):
        return filter(lambda c: self.compute_clause(c) == -1, self.clauses)

    def pick_branching_variable(self):
        positive = {x: 0 for x in self.vars if self.assigns[x] == -1}
        negative = {x: 0 for x in self.vars if self.assigns[x] == -1}
        for clause in self.all_unresolved_clauses():
            for v in clause:
                try:
                    if v > 0:
                        positive[v] += 1
                    else:
                        negative[abs(v)] += 1
                except KeyError:
                    pass
        pos_count = max(positive.items(), key = operator.itemgetter(1))
        neg_count = max(negative.items(), key = operator.itemgetter(1))
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

    def unit_propagate(self):
        while True:
            propagate_queue = []
            all_clauses = list(self.clauses.union(self.learnts))
            for clause in all_clauses:
                val = self.compute_clause(clause)
                if val == 1:
                    continue
                if val == 0:
                    return clause
                else:
                    unit_literal = self.get_unit_literal(clause)
                    if unit_literal == None:
                        continue
                    prop_pair = (unit_literal, clause)
                    if prop_pair not in propagate_queue:
                        propagate_queue.append(prop_pair)
            if propagate_queue == []:
                return None

            for prop_literal, clause in propagate_queue:
                prop_var = abs(prop_literal)
                if prop_literal > 0:
                    self.assigns[prop_var] = 1
                else:
                    self.assigns[prop_var] = 0
                self.update_implication(prop_var, clause)
                try:
                    self.propagate_history[self.level].append(prop_literal)
                except KeyError:
                    pass
    
    def get_assign_history(self):
        return [self.branching_history[self.level]] + self.propagate_history[self.level]

    def conflict_analyze(self, conf_cls):

        def next_recent_assigned(clause):
            for v in reversed(assign_history):
                if v in clause or -v in clause:
                    return v, [x for x in clause if abs(x) != abs(v)]

        if self.level == 0:
            return -1, None

        assign_history = self.get_assign_history()

        pool_lits = conf_cls
        done_lits = set()
        curr_level_lits = set()
        prev_level_lits = set()

        while True:
            for lit in pool_lits:
                if self.nodes[abs(lit)].level == self.level:
                    curr_level_lits.add(lit)
                else:
                    prev_level_lits.add(lit)

            if len(curr_level_lits) == 1:
                break

            last_assigned, others = next_recent_assigned(curr_level_lits)

            done_lits.add(abs(last_assigned))
            curr_level_lits = set(others)

            pool_clause = self.nodes[abs(last_assigned)].clause
            pool_lits = [
                l for l in pool_clause if abs(l) not in done_lits
            ] if pool_clause is not None else []

        learnt = frozenset([l for l in curr_level_lits.union(prev_level_lits)])
        if prev_level_lits:
            level = max([self.nodes[abs(x)].level for x in prev_level_lits])
        else:
            level = self.level - 1
        return level, learnt

    def backtrack(self, level):
        for var, node in self.nodes.items():
            if node.level <= level:
                node.children[:] = [child for child in node.children if child.level <= level]
            else:
                node.value = -1
                node.level = -1
                node.children = []
                node.clause = None
                self.assigns[node.variable] = -1

        levels = list(self.propagate_history.keys())
        for lvl in levels:
            if lvl <= level:
                continue
            del self.branching_history[lvl]
            del self.propagate_history[lvl]

class Node:
    def __init__(self, var):
        self.variable = var
        self.value = -1
        self.level = -1
        self.children = []
        self.clause = None

for i in range(5):
    index = i + 1
    st = 'cnf/uf75-0%d.cnf' % index
    s = Solver(st)
    print(s.solve())