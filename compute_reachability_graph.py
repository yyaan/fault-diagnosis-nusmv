import sys
import subprocess
import re
import os
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

    temp = output[output.index("REACHABILITY GRAPH") : output.index("LIVENESS ANALYSIS")]
    lines = temp.split('\n')
    transitions = set()
    max_state = 0

    code = ""

    transition_function = ""
    for line in lines:
        if '->' not in line:
            continue
        max_state += 1
        linesplit = line.replace(',','').replace('->','').split()
        next_state = dict()
        for tr in linesplit[1:]:
            transition_name = tr[:tr.index('/')]
            if transition_name in next_state.keys():
                next_state[transition_name] += [tr[tr.index('/')+1:]]
            else:
                next_state[transition_name] = [tr[tr.index('/')+1:]]
        
        for k in next_state.keys():
            transitions.add(k)
            x = "{"
            for v in next_state[k]:
                x += "{},".format(v)
            x = x[:-1] + "}"

            newline = "\t\tcurrent_state = " + linesplit[0] + " & transition = " + k + " : " + x
            transition_function += newline + ";\n"

    code = "MODULE fsa(can_move)\n\nVAR\n\ttaken_tansition: {visible, unvisible, fault, recovery};\n\tcurrent_state: 0.." + str(max_state-1) + ";\n"
    code += "\tsimulated_next_state : 0.." + str(max_state-1) + ";\n"

    trans = "{"
    for t in transitions:
        trans += "{},".format(t)
    trans = trans[:-1] + "}"

    code += "\ttransition: {};\n".format(trans)
    code += "\ttransition_type : {visible, unvisible, fault, recovery}; -- used to classify the current transition\n"
    code += "\timplicit_transition_taken : boolean;\n\thas_not_moved : boolean;\nINIT\n\tcurrent_state = 0 & taken_tansition = visible;\n\nASSIGN\n\n\tsimulated_next_state :=\n\tcase\n"

    code += transition_function + "TRUE : current_state;\n\tesac;\n\
\
    next(has_not_moved) := current_state = next(current_state);\n\
	next(current_state) :=\n\
	case can_move : simulated_next_state;\n\
	TRUE : current_state;\n\
	esac;\n\
\n\
	next(taken_tansition) :=\n\
	case can_move : transition_type;\n\
	TRUE : taken_tansition;\n\
	esac;\n\
\n\
	implicit_transition_taken := simulated_next_state = current_state;\n\
\n\
	transition_type :=\n\
	case\n\
		implicit_transition_taken : taken_tansition;\n\
	    transition = a | transition = b | transition = c : visible;\n\
	    transition = u : unvisible;\n\
	    transition = f : fault;\n\
	    transition = r : recovery;\n\
		TRUE : taken_tansition;\n\
	esac;\n\
\n\
-- END MODULE\n"
    return code



def run_tina(k, label, filename):
    code = generate_petri_net(k, label)
    f = open(filename, 'w')
    f.write(code)
    f.close()

    out = subprocess.check_output(["tina", "-R", "-lt", filename])
    return parse_output(out.decode())



# =======================================================
# usage python compute_reachability_graph.py K [a | b]

if len(sys.argv) != 3:
    print("Number of arguments is not valid")
    exit(1)
k = int(sys.argv[1])
lab = sys.argv[2]


custom = run_tina(k, lab, "example.net")
#os.unlink("example.net")
structure = open("structure.smv").read()

f = open("final_model.smv", 'w')

f.write(custom + "\n" + structure)

f.close()