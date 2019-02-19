import json

sha3_c_template = '''#include <stdlib.h>
#include <stdint.h>

#include "Hacl_SHA3.h"

extern void Lib_PrintBuffer_print_compare_display(uint32_t x0, uint8_t *x1, uint8_t *x2);

{0}

{1}

static void test_sha3 (
  uint32_t msg_len,
  uint32_t output_len,
  uint8_t *msg,
  uint8_t *expected
) {{
    uint8_t msg_[msg_len];
    memset(msg_, 0U, msg_len * sizeof msg_[0U]);
    memcpy(msg_, msg, msg_len * sizeof msg[0U]);
    uint8_t test_out[output_len];
    memset(test_out, 0U, output_len * sizeof test_out[0U]);
    {3}(msg_len, msg_, test_out);
    Lib_PrintBuffer_print_compare_display(output_len, test_out, expected);
}}

int32_t main() {{
    {2}
    return EXIT_SUCCESS;
}}
'''

test_template = 'static uint8_t test{0}_plaintext[{1}] = {{ {2} }};'
expected_template = 'static uint8_t test{0}_expected[{1}] = {{ {2} }};'
call_template = 'test_sha3 ({0}, {1}, test{2}_plaintext, test{2}_expected);'

def print_bytes(bytes):
    return ', '.join(bytes)

def to_list_of_bytes(m, m_len):
    bytes = list(map((lambda b: '(uint8_t)0x' + b + 'U'), (m[i: i+2] for i in range(0, len(m), 2))))
    bytes_len = len(bytes) * 8
    if m_len == 0:
        assert(bytes_len == 8)
    else:
        assert (bytes_len == m_len)
    return bytes

def main():
    with open('generated/json/fips-202.json', 'r') as tests_file:
        tests = tests_file.read()
    j = json.loads(tests)
    fun_name = j['SHA3']['HACL']
    for test_suite in j['SHA3']['suites']:
        md_len = int(j['SHA3']['suites'][test_suite]['MDLen'])
        call_name = fun_name + j['SHA3']['suites'][test_suite]['suffix']
        test_list, expected_list, call_list = [], [], []
        for i, test in enumerate(j['SHA3']['suites'][test_suite]['vectors']):
            msg_bytes = to_list_of_bytes(test['Msg'], int(test['Len']))
            md_bytes = to_list_of_bytes(test['MD'], md_len)
            msg_bytes_len = str(len(msg_bytes)) + 'U'
            md_bytes_len = str(len(md_bytes)) + 'U'
            test_list.append(test_template.format(str(i), msg_bytes_len, print_bytes(msg_bytes)))
            expected_list.append(expected_template.format(str(i), md_bytes_len, print_bytes(md_bytes)))
            call_list.append(call_template.format(msg_bytes_len, md_bytes_len, str(i)))
        with open('generated/c/' + test_suite + '.c', 'w') as c_file:
            c_file.write(sha3_c_template.format(
                '\n'.join(test_list),
                '\n'.join(expected_list),
                '\n    '.join(call_list),
                call_name
            ))
main()
