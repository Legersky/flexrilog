## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests


# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib --show-skipped flexrilog")
        if errno != 0:
            sys.exit(1)

setup(
    name = "flexrilog",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='FlexRiLoG - A package for investigating Flexible and Rigid Labelings of Graphs',
    long_description = readfile("README.rst"), # get the long description from the README
    url='https://github.com/legersky/flexrilog',
    author='Jan Legerský, Georg Grasegger',
    author_email='jan.legersky@risc.jku.at', # choose a main contact email
    license='GPLv3+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 3 - Alpha',
      'Intended Audience :: Science/Research',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)',
      'Programming Language :: Python :: 2.7',
    ],
    keywords = "rigidity flexibility",
    packages = ['flexrilog'],
    cmdclass = {'test': SageTest}, # adding a special setup command for tests
    setup_requires   = ['sage-package'],
    install_requires = ['sage-package', 'sphinx'],
)
