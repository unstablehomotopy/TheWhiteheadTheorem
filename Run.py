import re
import sys
import os
import subprocess

# To run, let PATH be the full file name including the path of this python3 file. 
# For me, this is /Users/secure/Documents/Workflow/Run.py
# Let PATH2 be teh full file name of the .tex file to be run. 
# E.g. /Users/secure/Documents/ExampleFolder/ExampleSubfolder/Example.tex
# Then the terminal command to compile is:
# "shell_cmd": "python3 /Users/secure/Documents/Workflow/Run.py $file"




PP1 = sys.argv[0]
PP2 = sys.argv[1]


############################################################
#########################  SETUP  ##########################
############################################################

pieces = PP1.split("/")
n = len(pieces)

workflow = ""
for i in range(n-1):
    workflow = workflow + pieces[i]
    workflow = workflow + "/"
workflow = workflow[0:-1]

pieces = PP2.split("/")
n = len(pieces)

name = pieces[-1].split(".")[0]

basefile = ""
for i in range(n-1):
    basefile = basefile + pieces[i]
    basefile = basefile + "/"
basefile = basefile[0:-1]

prepath = basefile + "/" + name + "/"

path = basefile + "/" + name + "/" + name + ".tex"


f = open(basefile + "/" + name + ".tex", "r")
text = f.read()

text = text.replace("\\", "")


###########################################################
######################## PARSER ###########################
###########################################################

def match(X, S, i):
    matches = True
    for j in range(len(S)):
        if not (i + j < len(X)) or  not (j < len(S)):
            matches = False
        elif (S[j] != X[i+j]):
            matches = False
    return matches


def EXTRACT(X, command):
    RESULTS = []
    i = 0
    while (i < len(X)):
        if match(X, command, i):
            i  = i + len(command)
            while match(X, " ", i):
                i = i + 1
            try:
                assert match(X, r"{", i)
            except:
                print("")
            i = i +1
            level = 0
            J = i
            RESULT = ""
            while not ((X[i-1] == "d") and (X[i-2] == "e") and (X[i-3] == "t") and (X[i-4] == "n") ):
                RESULT = RESULT + X[i]
                i = i + 1
            RESULTS.append(RESULT)
            if i >= len(X):
                print("ERROR: mismatched parentheses starting at " + str(J))
        i = i + 1
    return RESULTS




###########################################################
#####################   RUN LEAN   ########################
###########################################################
"""
# Make a new lean file
try:

    terminal_command = "cd; cd " + basefile + " ; lake new " + name  + " > /dev/null 2>&1"
    os.system(terminal_command)
except:
    pass


# Copy name.top to name.tex in basefile/name
try:
    name1 = basefile + "/" + name + "/" + name + ".tex"
    name2 = basefile+ "/" + name + ".tex"
    f = open(name1, "a")
    g = open(name2, "r")
    text2 = g.read()
    f.truncate(0)
    f.write(text2)

    g.close()
    f.close()
except:
    print("Trouble creating tex file; see New.py line 42")
"""












#________________________________________
# 20 MIN
"""
- For each entry of the list,
-- Replace "\n" with "NEWLINE"
-- Replace "\\ \\"" with "NEWLINE"
-- Replace "\iffalse" with "/-""
-- Replace "\fi" with "-/""
-- Replace "%.../n" with "/-...-/" [... shouldn't match /n]
-- Replace "NEWLINE..spaces..NEWLINE" with "\n"
-- Replace ...
"""


prints = EXTRACT(text, "\\print")
blocks = EXTRACT(text, r"lean}")
preblocks = text.split(r"lean}")
block_lengths = []
for block in preblocks:
    block_lengths.append(block.count("\n"))
code = ""
counter = 0
counter2 = 0
for i in range(len(blocks)):
    block = blocks[i]
    counter2 = counter2 + block_lengths[i]
    code = code + block[0:len(block)-10]
    counter = counter + 1





g = open("/Users/elliotyoung/Documents/Math/TheWhiteheadTheorem/TheWhiteheadTheorem/TheWhiteheadTheorem.lean", "r")
categories = ""    #g.read()

leanfile = prepath + ((name + ".tex").split(".")[0])
with open(leanfile + ".lean", "r+") as g:
    data = g.read()
    g.seek(0)
    g.write(code)
    g.truncate()
    g.close()

a = ''

code = code +'def main : IO UInt32 := do {return 0;}'

with open(prepath + "Main" + ".lean", "r+") as h:
    data = h.read()
    h.seek(0)
    h.truncate(0)
    if (name != "Categories"):
        h.write(categories)
    h.write(code)
    h.truncate()
    h.close()

os.system("cd; cd " + prepath[0:len(prepath)-1]  + "; " + " lake build " + name)


command = "cd ; cd " + prepath[0:len(prepath)-1] + "; " + "lean --run Main.lean > " + "output.txt"

os.system(command)

#Open the resulting .txt file

output = open(prepath + "output.txt", "r")
output = output.read()

P = output.split("PRINT")
for i in range(len(P)):
    P[i] = P[i][2:len(P[i])]
for i in range(1, len(P)):
    with open(prepath + str(i)+ ".txt", "a") as f:
        f.seek(0);
        f.truncate(0);
        f.write(P[i]);
        f.close();

# print("\n\nLEAN OUTPUT:\n")
print(output)






###########################################################
####################   RUN python3   ######################
###########################################################


"""
command = "cd; cd "+ prepath[0:len(prepath)-1] + "; " + "clang program.c -o program"
"""



blocks = EXTRACT(text, r"{python}")
preblocks = text.split(r"{python}")
block_lengths = []
for block in preblocks:
    block_lengths.append(block.count("\n"))
code = ""
counter = 0
counter2 = 0
for i in range(len(blocks)):
    block = blocks[i]
    counter2 = counter2 + block_lengths[i]
    code = code + block[0:len(block)-11]
    counter = counter + 1



pfile = prepath + ((name + ".tex").split(".")[0])
with open(pfile + ".py", "r+") as g:
    data = g.read()
    g.seek(0)
    g.write(code)
    g.truncate()
    g.close()

#code = 'import Init.Data.ToString.Basic\n\nimport Mathlib.Tactic.LibrarySearch' + code

"""
if (len(prints) > 0):
    line = 'def STRING0 := "PRINT' + ': " ++ (toString ' + prints[0] + ') ++ "\\n\\n"'
    code = code + line + "\n\n"

    for i in range(1, len(prints)):
        newline = 'def STRING' + str(i) + ':= STRING' + str(i-1) + ' ++ "PRINT' + ': " ++ (toString ' + prints[i] + ') ++ "\\n\\n"'
        code = code + newline + "\n\n"
    code = code + "def main : IO Unit := IO.println STRING" + str(len(prints)-1)
else:
"""

with open(prepath + name + ".py", "r+") as h:
    data = h.read()
    h.seek(0)
    h.truncate(0)
    h.write(code)
    h.truncate()
    h.close()


os.system("cd; cd " + prepath[0:len(prepath)-1]  + "; " + "  " + name)


command = "cd ; cd " + prepath[0:len(prepath)-1] + "; " + "python3 " + name +".py" + " > output3.txt"




os.system(command)


#print("\n\nPYTHON OUTPUT:\n")
#output = open(prepath + "output3.txt", "r")
#output = output.read()
#print(output)

#Open the resulting .txt file

"""
output = open(prepath + "output3.txt", "r")
output = output.read()

P = output.split("PRINT")
for i in range(len(P)):
    P[i] = P[i][2:len(P[i])]
for i in range(1, len(P)):
    with open(prepath + str(i)+ ".txt", "a") as f:
        f.seek(0);
        f.truncate(0);
        f.write(P[i]);
        f.close();
"""




###########################################################
###################        RUN C       ####################
###########################################################

"""
command = "cd; cd "+ prepath[0:len(prepath)-1] + "; " + "clang program.c -o program"
"""


prints = EXTRACT(text, "\\print")
blocks = EXTRACT(text, r"|]{c}")
preblocks = text.split(r"end{c")
block_lengths = []
for block in preblocks:
    block_lengths.append(block.count("\n"))
code = ""
counter = 0
counter2 = 0
for i in range(len(blocks)):
    block = blocks[i]
    counter2 = counter2 + block_lengths[i]
    code = code + block[0:len(block)-11]
    counter = counter + 1


cfile = prepath + ((name + ".tex").split(".")[0])
with open(cfile + ".c", "r+") as g:
    data = g.read()
    g.seek(0)
    g.write(code)
    g.truncate()
    g.close()

"""
if (len(prints) > 0):
    line = 'def STRING0 := "PRINT' + ': " ++ (toString ' + prints[0] + ') ++ "\\n\\n"'
    code = code + line + "\n\n"

    for i in range(1, len(prints)):
        newline = 'def STRING' + str(i) + ':= STRING' + str(i-1) + ' ++ "PRINT' + ': " ++ (toString ' + prints[i] + ') ++ "\\n\\n"'
        code = code + newline + "\n\n"
    code = code + "def main : IO Unit := IO.println STRING" + str(len(prints)-1)
else:
"""


with open(prepath + "Main" + ".lean", "r+") as h:
    data = h.read()
    h.seek(0)
    h.truncate(0)
    h.write(code)
    h.truncate()
    h.close()


os.system("cd; cd " + prepath[0:len(prepath)-1]  + "; " + "  " + name)

command = "cd ; cd " + prepath[0:len(prepath)-1] + "; " + "clang " + name + ".c -o " + name +";"+" ./" + name + " > " + "output2.txt"



os.system(command)

#Open the resulting .txt file

output = open(prepath + "output2.txt", "r")
output = output.read()

P = output.split("PRINT")
for i in range(len(P)):
    P[i] = P[i][2:len(P[i])]
for i in range(1, len(P)):
    with open(prepath + str(i)+ ".txt", "a") as f:
        f.seek(0);
        f.truncate(0);
        f.write(P[i]);
        f.close();

#print("\n\nC OUTPUT:\n")
#print(output)












###########################################################
###################     RUN LATEX     #####################
###########################################################

print( "right here")
command = "cd; cd Documents; cd Math; cd TheWhiteheadTheorem; xelatex -shell-escape TheWhiteheadTheorem.tex"
os.system(command)
os.system("cd; cd Documents; cd Math; cd TheWhiteheadTheorem; open " + name + ".pdf")





