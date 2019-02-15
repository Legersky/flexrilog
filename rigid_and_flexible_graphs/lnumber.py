from os import getcwd
from os import path as os_path
from sys import path
from ctypes import cdll, c_char, c_size_t

path.insert(0, getcwd())
dir_path = os_path.dirname(os_path.realpath(__file__))
lib = cdll.LoadLibrary(os_path.join(dir_path, "lnumber.pyd"))

def lnumber(graph, verts):
  global lib
  return lib.laman_number(str(graph).encode("utf-8"), c_size_t(verts))

#print lnumber(252590061719913632,12)
