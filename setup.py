# This is your "setup.py" file.
# See the following sites for general guide to Python packaging:
#   * `The Hitchhiker's Guide to Packaging <http://guide.python-distribute.org/>`_
#   * `Python Project Howto <http://infinitemonkeycorps.net/docs/pph/>`_

from setuptools import setup, find_packages
import sys, os
#from Cython.Build import cythonize
from setuptools.extension import Extension

here = os.path.abspath(os.path.dirname(__file__))
README = open(os.path.join(here, 'README.rst')).read()
NEWS = open(os.path.join(here, 'NEWS.rst')).read()


version = '0.1'

install_requires = [
    # List your project dependencies here.
    # For more details, see:
    # http://packages.python.org/distribute/setuptools.html#declaring-dependencies
    # Packages with fixed versions
    # "<package1>==0.1",
    # "<package2>==0.3.0",
    # "nose", "coverage"   # Put it here.
]

tests_requires = [
    # List your project testing dependencies here.
]

dev_requires = [
    # List your project development dependencies here.\
]

dependency_links = [
    # Sources for some fixed versions packages
    #'https://github.com/<user1>/<package1>/archive/master.zip#egg=<package1>-0.1',
    #'https://github.com/<user2>/<package2>/archive/master.zip#egg=<package2>-0.3.0',
]

#Cython extension

#TOP_DIR="/home/eugeneai/Development/codes/NLP/workprog/tmp/link-grammar"
#LG_DIR="link-grammar"
#LG_LIB_DIR=os.path.join(TOP_DIR,LG_DIR,".libs")
#LG_HEADERS=os.path.join(TOP_DIR)

ext_modules=[
#    Extension("bib-analyzer.cython_module",
#              sources=["src/./bib-analyzer/cython_module.pyx"],
#              libraries=["gdal"],
#    )
]

setup(
    name='bib-analyzer',
    version=version,
    description="Analyzer of referencess in dissertations in Russian",
    long_description=README + '\n\n' + NEWS,
    # Get classifiers from http://pypi.python.org/pypi?%3Aaction=list_classifiers
    # classifiers=[c.strip() for c in """
    #     Development Status :: 4 - Beta
    #     License :: OSI Approved :: MIT License
    #     Operating System :: OS Independent
    #     Programming Language :: Python :: 2.6
    #     Programming Language :: Python :: 2.7
    #     Programming Language :: Python :: 3
    #     Topic :: Software Development :: Libraries :: Python Modules
    #     """.split('\n') if c.strip()],
    # ],
    keywords='nlp dissertation bibliography recognition',
    author='Nikolay Kapyrin, Evgeny Cherkashin (packaging)',
    author_email='nikolay.kapyrin@gmail.com, eugeneai@irnok.net',
    url='https://github.com/eugeneai/bib-analyzer',
    license='GPLv3',
    packages=find_packages("src"),
    package_dir = {'': "src"},    include_package_data=True,
    zip_safe=False,
    install_requires=install_requires,
    dependency_links = dependency_links,
    extras_require={
          'tests': tests_requires,
          'dev': dev_requires,
    },
    test_suite='tests',
    entry_points={
        'console_scripts':
            ['bib-analyzer=bibanalyzer:main']
    },
    #ext_modules = cythonize(ext_modules),
    #test_suite = 'nose.collector',
    #setup_requires=['nose>=1.0','Cython','coverage']
)
