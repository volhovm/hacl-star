import re
import json
import itertools
from os import listdir


hacl_funs = {
    "SHA3": "Hacl_SHA3_sha3",
}

regex_rsp_l = r'\[L = (?P<md_len>\d+)\]\s+'
regex_rsp_len = r'Len = (?P<len>\w+)\s+'
regex_rsp_msg = r'Msg = (?P<msg>\w+)\s+'
regex_rsp_md = r'MD = (?P<md>\w+)\s+'

def parse_rsp(suite_name, f):
    tests = []
    for _, g in itertools.groupby(list(f), (lambda l: l == '\n')):
        g = list(g)
        if g != ['\n']:
            tests.append(g)
    tests = tests[1:] # discard initial comments
    md_len = re.search(regex_rsp_l, tests[0][0]).group('md_len')

    vectors = []
    for v in tests[1:]:
        test_len = re.search(regex_rsp_len, v[0]).group('len')
        test_msg = re.search(regex_rsp_msg, v[1]).group('msg')
        test_md = re.search(regex_rsp_md, v[2]).group('md')
        vectors.append({'Len': test_len, 'Msg': test_msg, 'MD': test_md})
    return {suite_name: {'suffix': "_" + md_len, 'MDLen': int(md_len), 'vectors': vectors}}

def main():
    path = 'fips-202'
    files = listdir(path)
    suites = {}
    for rsp in files:
        assert (rsp[-4:] == '.rsp')
        suite_name = rsp[:-4]
        with open(path + '/' + rsp, 'r') as f:
            suites.update(parse_rsp(suite_name, f))
    j = {'SHA3': {'HACL': hacl_funs['SHA3'], 'suites': suites}}
    with open('generated/json/' + path + '.json', 'w') as f:
         json.dump(j, f, indent=2, separators=(',', ': '))


main ()
