# This scripts is used to execute the algorithm and to generate the NUSMV code according to the authors approach.
import sys
import subprocess
import re
import os 

START = 0
class Node:
    def __init__(self, nodeid):
        if isinstance(nodeid, Node):
            self.id = nodeid.id
            self.label = str(nodeid.label)
        else:
            self.id = nodeid
            self.label = None
    
    def set_label(self, label):
        self.label = label
    
    def get_label(self):
        return self.label

    def __str__(self):
        if hasattr(self, 'id1'):
            return "({} {} {} {})".format(self.id1, self.label1,self.id2, self.label2)
        else:
            return "({} {})".format(self.id, self.label)
    

class Graph:

    def __init__(self):
        self.adj = dict()
        self.nodes = set()

    def add_node(self, node):
        nl = "" if node.label is None else node.label
        if (node.id, nl) not in self.adj.keys():
            self.adj[(node.id, nl)] = set()
            self.nodes.add(node)
    
    def add_edge(self, node1, node2, edge):
        nl = "" if node1.label is None else node1.label
        self.adj[(node1.id,nl)].add((node2, edge))
    
    def get_neighbors(self, node):
        nl = "" if node.label is None else node.label
        return self.adj[(node.id, nl) ]
    
    def get_transitions(self, node):
        transitions = dict()
        for n in self.get_neighbors(node):
            if n[1] in transitions.keys():
                transitions[n[1]] += [n[0]]
            else:
                transitions[n[1]] = [n[0]]
        return transitions

    def get_node(self, nodeid, label=None):
        for n in self.nodes:
            if n.id == nodeid and (label is None or label == n.get_label()):
                return n

    def __len__(self):
        return len(self.adj.keys())
    
    def __str__(self):
        string = ""
        for k in self.adj.keys():
            adjs = ""
            for n in self.adj[k]:
                adjs += "({} {})/{} ".format(n[0].id, n[0].label, n[1])
            string += "{} -> {}\n".format(k, adjs)
        return string

class PGraph:

    def __init__(self):
        self.adj = dict()
        self.nodes = set()

    def add_node(self, node):
        a = (node.id1, node.label1, node.id2, node.label2)
        if a not in self.adj.keys():
            self.adj[a] = set()
            self.nodes.add(node)
    
    def add_edge(self, node1, node2, edge):
        a = (node1.id1, node1.label1, node1.id2, node1.label2)
        self.adj[a].add((node2, edge))
    
    def get_neighbors(self, node):
        a = (node.id1, node.label1, node.id2, node.label2)
        return self.adj[a]
    
    def __len__(self):
        return len(self.adj.keys())
    
    def get_node(self, n1, n2, label=None):
        for n in self.nodes:
            if n.id1 == n1 and n.id2 == n2 and (label is None or (label == n.label1 and label == n.label2)):
                return n
    
    def __str__(self):
        string = ""
        for k in self.adj.keys():
            adjs = ""
            for n in self.adj[k]:
                adjs += "{}/{} ".format(n[0], n[1])
            string += "{} -> {}\n".format(k, adjs)
        return string


def generate_petri_net(k, label):

    code =""
    code += "tr t1_1 : a [0,w[ p0 -> p1_1\n"
    t1_1_2 = ""

    for i in range(k):
        t1_1_2 += "p1_1_3_{} ".format(i+1)
    code += "tr t1_1_2 : b [0,w[ p1_1 -> {}\n".format(t1_1_2)

    for i in range(k):
        code += "tr t1_1_3_{} : u [0,w[ p1_1_3_{} -> p1_1_4_{}\n".format(1+i, 1+i, 1+i)
        code += "tr t1_1_4_{} : c [0,w[ p1_1_4_{} -> p1_1_5_{}\n".format(1+i, 1+i, 1+i)
    
    p1_1_5 = ""
    for i in range(k):
        p1_1_5 += "p1_1_5_{} ".format(i+1)
    code += "tr t1_1_5 : u [0,w[ {} -> p1_1\n".format(p1_1_5)

    # ==== RIGHT PART

    code += "tr t1_2 : {} [0,w[ p0 -> p1_2\n".format(label)
    t1_2_2 = ""

    for i in range(k):
        t1_2_2 += "p1_2_3_{} ".format(i+1)
    code += "tr t1_2_2 : b [0,w[ p1_2 -> {}\n".format(t1_2_2)

    for i in range(k):
        if i == 0:
            code += "tr t1_2_3_{} : f [0,w[ p1_2_3_{} -> p1_2_4_{}\n".format(1+i, 1+i, 1+i)
        else:
            code += "tr t1_2_3_{} : u [0,w[ p1_2_3_{} -> p1_2_4_{}\n".format(1+i, 1+i, 1+i)
        code += "tr t1_2_4_{} : c [0,w[ p1_2_4_{} -> p1_2_5_{}\n".format(1+i, 1+i, 1+i)
    
    p1_2_5 = ""
    for i in range(k):
        p1_2_5 += "p1_2_5_{} ".format(i+1)
    code += "tr t1_2_5 : r [0,w[ {} -> p1_2\n".format(p1_2_5)
    code += "pl p0 (1)"
    return code

def parse_output(output):

    graph = Graph()

    temp = output[output.index("REACHABILITY GRAPH") : output.index("LIVENESS ANALYSIS")]
    lines = temp.split('\n')
   
    for line in lines:
        if '->' not in line:
            continue
        linesplit = line.replace(',','').replace('->','').split()
        n0 = Node(int(linesplit[0]))
        graph.add_node(n0)

        next_state = dict()
        for tr in linesplit[1:]:
            transition_name = tr[:tr.index('/')]
            value = int(tr[tr.index('/')+1:])
            nvalue = Node(value)
            graph.add_node(nvalue)
            graph.add_edge(n0, nvalue, transition_name)
    return graph


def run_tina(k, label, filename):
    code = generate_petri_net(k, label)
    f = open(filename, 'w')
    f.write(code)
    f.close()

    out = subprocess.check_output(["tina", "-R", "-lt", filename])

    
    return parse_output(out.decode())

def labeling(graph):

    lbgraph = Graph()

    startNode = graph.get_node(START)
    queue = list()
    queue.append((startNode, 'NORMAL'))
    currentNode = Node(startNode.id)
    currentNode.set_label('NORMAL')
    lbgraph.add_node(currentNode)
    visited = set()
    
    while len(queue) > 0:

        current_node, current_label = queue.pop()
        current_lb_node = lbgraph.get_node(current_node.id, current_label)
        visited.add((current_node.id, current_label))
        
        for neighbor, edge in graph.get_neighbors(current_node):
            new_neighbor = Node(neighbor.id)
            if edge == 'f' and current_label != 'FAULT':
                new_neighbor.set_label('FAULT')
            elif edge == 'r' and current_label == 'FAULT':
                new_neighbor.set_label('RESET')
            else:
                new_neighbor.set_label(current_label)
            

            if (new_neighbor.id, new_neighbor.get_label()) not in visited:
                lbgraph.add_node(new_neighbor)
                queue.append((neighbor, new_neighbor.get_label()))
            lbgraph.add_edge(current_lb_node, new_neighbor, edge)
    return lbgraph

def projection(labeled_graph):
    projection_graph = Graph()
    startNode = labeled_graph.get_node(START, 'NORMAL')
    queue = list()
    queue.append((startNode, startNode))
    projection_graph.add_node(startNode)

    visited = set()
    invisible_edges = ['u', 'r', 'f']
    visited.add((startNode.id, startNode.label, startNode.id, startNode.label))
    while len(queue)>0:

        current_node, last_visible = queue.pop()

        for node, edge in labeled_graph.get_neighbors(current_node):
            # if edge is normal add new node to graph
            current_last_visible = last_visible
            if (node.id, node.label, last_visible.id, last_visible.label) not in visited:
                projection_graph.add_node(node)
        
            if edge not in invisible_edges:
                projection_graph.add_edge(last_visible, node, edge)
                current_last_visible = node
            
            if (node.id, node.label, current_last_visible.id, current_last_visible.label) not in visited:
                queue.append((node, current_last_visible))
                visited.add((node.id, node.label, current_last_visible.id, current_last_visible.label))

    return projection_graph

def convert_nusmv(graph):

    transition_function = ""

    state_name = ""

    state_label = ""

    # assign to each state a new id
    node_map = dict()
    id_map = dict()
    max_state = 0
    id_start_state = 0
    for i, k in enumerate(graph.adj.keys()):
        node_map[k] = i
        id_map[i] = k
        max_state = i
        if k[0] == START:
            id_start_state = i

    
    for node_id, label in graph.adj.keys():
        transitions = dict()

        for node, edge in graph.adj[(node_id, label)]:
            if edge in transitions.keys():
                transitions[edge] += [(node.id, node.label)]
            else:
                transitions[edge] = [(node.id, node.label)]
        for k in transitions.keys():
            next_states = ""
            for v in transitions[k]:
                next_states += "{},".format(node_map[v])
            transition_function += "\tcurrent_state = " + str(node_map[(node_id, label)]) + " & transition = " + k + " : " + "{" + next_states[:-1] + "};\n"
    
    state_names = set()
    for nid in id_map.keys():
        state_names.add(id_map[nid][0])
        state_name += "\tcurrent_state = " + str(nid) + " : " + str(id_map[nid][0]) + ";\n"
        state_label += "\tcurrent_state = " + str(nid) + " : " + id_map[nid][1] + ";\n"
    
    state_names_string = "\tstate_name : {"
    for sn in state_names:
        state_names_string += str(sn) + ","
    state_names_string = state_names_string[:-1] + "};\n"

    code = "MODULE fsa(transition, other_implicit)\n\nVAR\n\tcurrent_state: 0..{};\n".format(max_state)
    code += "\timplicit_transition_taken : boolean;\n\tsimulated_next_state : 0..{};\n".format(max_state)
    code += state_names_string + "\tstate_label : {NORMAL, FAULT, RESET};\n\nINIT\n"
    code += "\tcurrent_state = {} & implicit_transition_taken = FALSE;\n".format(id_start_state)
    code += "ASSIGN\n\timplicit_transition_taken := simulated_next_state = current_state;\n\tsimulated_next_state := case\n" + transition_function +  "\tTRUE : current_state;\n\tesac;\n\n"
    code += "\tnext(current_state) := case\n\t! other_implicit : simulated_next_state;\n\tTRUE : current_state;\nesac;\n"
    code +="\tstate_name := case\n" + state_name + "\n\tesac;\n\n \tstate_label := case\n" + state_label + "\tesac;\n"
    return code


def convert_nusmv_prod(graph):

    transition_function = ""

    state1_name = ""
    state1_label = ""
    state2_name = ""
    state2_label = ""
    # assign to each state a new id
    node_map = dict()
    id_map = dict()
    max_state = 0
    id_start_state = 0
    for i, k in enumerate(graph.adj.keys()):
        node_map[k] = i
        id_map[i] = k
        max_state = i
        if k[0] == START and k[2] == START:
            id_start_state = i
    
    for node1_id, node1_lab, node2_id, node2_lab in graph.adj.keys():
        a = (node1_id, node1_lab, node2_id, node2_lab)

        transitions = dict()

        for node, edge in graph.adj[a]:
            if edge in transitions.keys():
                transitions[edge] += [(node.id1, node.label1,node.id2, node.label2)]
            else:
                transitions[edge] = [(node.id1, node.label1,node.id2, node.label2)]
        for k in transitions.keys():
            next_states = ""
            for v in transitions[k]:
                next_states += "{},".format(node_map[v])
            transition_function += "\tcurrent_state = " + str(node_map[a]) + " & transition = " + k + " : " + "{" + next_states[:-1] + "};\n"
    
    state_names = set()
    for nid in id_map.keys():
        state_names.add(id_map[nid][0])
        state_names.add(id_map[nid][2])
        state1_name += "\tcurrent_state = " + str(nid) + " : " + str(id_map[nid][0]) + ";\n"
        state1_label += "\tcurrent_state = " + str(nid) + " : " + id_map[nid][1] + ";\n"
        state2_name += "\tcurrent_state = " + str(nid) + " : " + str(id_map[nid][2]) + ";\n"
        state2_label += "\tcurrent_state = " + str(nid) + " : " + id_map[nid][3] + ";\n"
    
    state_names_string = " : {"
    for sn in state_names:
        state_names_string += str(sn) + ","
    state_names_string = state_names_string[:-1] + "};\n"

    state1_name_string = "\tstate1_name " + state_names_string
    state2_name_string = "\tstate2_name " + state_names_string
    state_names_string = state1_name_string + state2_name_string

    code = "MODULE fsa(transition)\n\nVAR\n\tcurrent_state: 0..{};\n".format(max_state)
    code += "\timplicit_transition_taken : boolean;\n"
    code += state_names_string + "\tstate1_label : {NORMAL, FAULT, RESET};\n\tstate2_label : {NORMAL, FAULT, RESET};\n\nINIT\n"
    code += "\tcurrent_state = {} & implicit_transition_taken = FALSE;\n".format(id_start_state)
    code += "ASSIGN\n\tnext(implicit_transition_taken) := next(current_state) = current_state;\n\tnext(current_state) := case\n" + transition_function +  "\tTRUE : current_state;\n\tesac;\n\n"
    code +="\tstate1_name := case\n" + state1_name + "\n\tesac;\n\n \tstate1_label := case\n" + state1_label + "\tesac;\n"
    code +="\tstate2_name := case\n" + state2_name + "\n\tesac;\n\n \tstate2_label := case\n" + state2_label + "\tesac;\n"
    return code


def product(g1, g2):

    pgraph = PGraph()

    startNode1 = g1.get_node(START, 'NORMAL')
    startNode2 = g2.get_node(START, 'NORMAL')
    ns = Node(0)
    ns.id1 = startNode1.id
    ns.label1 = startNode1.label
    ns.id2 = startNode2.id
    ns.label2 = startNode2.label
    pgraph.add_node(ns)

    queue = list()
    queue.append((ns, startNode1, startNode2))

    visited = set()
    visited.add((startNode1.id, startNode1.label, startNode2.id, startNode2.label))
    
    while len(queue)>0:

        pnode, node1, node2 = queue.pop()

        t1 = g1.get_transitions(node1)
        t2 = g2.get_transitions(node2)

        for k in t1.keys():
            if k in t2.keys():
                for v1 in t1[k]:
                    for v2 in t2[k]:
                        nn = Node(0)
                        nn.id1 = v1.id
                        nn.id2 = v2.id
                        nn.label1 = v1.label
                        nn.label2 = v2.label
                        
                        if (nn.id1, nn.label1, nn.id2, nn.label2) not in visited:
                            pgraph.add_node(nn)
                            visited.add((nn.id1, nn.label1, nn.id2, nn.label2))
                            queue.append((nn, v1, v2))
                        
                        pgraph.add_edge(pnode, nn, k)
    return pgraph



# =======================================================
if len(sys.argv) != 3:
    print("Number of arguments is not valid")
    exit(1)
k = int(sys.argv[1])
lab = sys.argv[2]


reach = run_tina(k, lab, "example.net")
print("Length reach graph: ", len(reach))
#os.unlink("example.net")
# g = Graph()

# node1 = Node(1)
# node2 = Node(2)
# node3 = Node(3)
# node4 = Node(4)
# node5 = Node(5)
# node6 = Node(6)
# node7 = Node(7)
# node8 = Node(8)

# g.add_node(node1)
# g.add_node(node2)
# g.add_node(node3)
# g.add_node(node4)
# g.add_node(node5)
# g.add_node(node6)
# g.add_node(node7)
# g.add_node(node8)

# g.add_edge(node1, node2, 'u')
# g.add_edge(node1, node3, 'a')
# g.add_edge(node2, node4, 'a')
# g.add_edge(node4, node6, 'b')
# g.add_edge(node6, node4, 'c')
# g.add_edge(node3, node5, 'f')
# g.add_edge(node5, node7, 'b')
# g.add_edge(node7, node8, 'r')
# g.add_edge(node8, node3, 'c')

# lab = labeling(g)

lab = labeling(reach)
print("Len labeling", len(lab))
x = projection(lab)
print(len(x))

final = product(x, x)
print("len product", len(final))
o = open("compiled_main.smv").read()
f = open("compiled_fsa.smv", 'w')
f.write( o + "\n" + convert_nusmv_prod(final))
f.close()
