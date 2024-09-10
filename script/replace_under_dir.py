import os
import sys
import re
import subprocess

regex = r"_failatwith __FILE__ __LINE__ "
subst = "_die_with [%here] "

regex = "module Nt = Normalty.Frontend"
subst = ""

regex = "Zzdatatype.Datatype"
subst = "Zdatatype"

regex = "open Sugar"
subst = ""

regex = "Nt.mk_tuple"
subst = "Nt.Ty_tuple"

# regex = "Ntopt"
# subst = "Nt"

# regex = r"__FILE__ __LINE__"
# subst = "[%here]"

# regex = r" file line "
# subst = " loc "

# regex = r"Nt.eq "
# subst = "Nt.equal_nt "

walk_dir = sys.argv[1]
tmp_path = "/tmp/.tmp"
tmp_original_path = "/tmp/.tmp_original"

print('walk_dir = ' + walk_dir)

# If your current working directory may change during script execution, it's recommended to
# immediately convert program arguments to an absolute path. Then the variable root below will
# be an absolute path as well. Example:
# walk_dir = os.path.abspath(walk_dir)
print('walk_dir (absolute) = ' + os.path.abspath(walk_dir))

for root, subdirs, files in os.walk(walk_dir):
    print('--\nroot = ' + root)
    if "_build" in root:
        continue
    for filename in files:
        if (os.path.splitext(filename)[-1] == ".ml") or (os.path.splitext(filename)[-1] == ".mly"):
            file_path = os.path.join(root, filename)
            print('\t- file %s (full path: %s)' % (filename, file_path))
            proc = subprocess.run(["cp", file_path, tmp_original_path], shell=False)
            if proc.returncode != 0:
                print("the mv fails")
                exit(1)
            with open(file_path, 'r+') as f:
                original_content = f.read()
                f_content = re.sub(regex, subst, original_content, 0, re.MULTILINE)
                f.seek(0)
                f.write(f_content)
                f.truncate()
            with open(tmp_path, 'w') as tmp:
                proc = subprocess.run(["ocamlformat", file_path], shell=False, stdout=tmp)
            if proc.returncode == 0:
                proc = subprocess.run(["mv", tmp_path, file_path], shell=False)
            else:
                proc = subprocess.run(["mv", tmp_original_path, file_path], shell=False)
                print("the command fails: {}".format(subprocess.list2cmdline(proc.args)))
                exit(1)
