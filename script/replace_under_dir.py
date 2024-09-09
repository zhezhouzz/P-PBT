import os
import sys
import re
import subprocess

regex = r"_failatwith __FILE__ __LINE__ \"die\""
subst = "_die [%here]"

regex = r"\[@@deriving sexp\]"
subst = "[@@deriving sexp, show, eq, ord]"

walk_dir = sys.argv[1]
tmp_path = "/tmp/.tmp"

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
        if os.path.splitext(filename)[-1] == ".ml":
            file_path = os.path.join(root, filename)
            print('\t- file %s (full path: %s)' % (filename, file_path))
            with open(file_path, 'r+') as f:
                f_content = f.read()
                f_content = re.sub(regex, subst, f_content, 0, re.MULTILINE)
                f.seek(0)
                f.write(f_content)
                f.truncate()
            with open(tmp_path, 'w') as tmp:
                proc = subprocess.run(["ocamlformat", file_path], shell=False, stdout=tmp)
            proc = subprocess.run(["mv", tmp_path, file_path], shell=False)
            # print("the commandline is {}".format(subprocess.list2cmdline(proc.args)))
