import sys
import hashlib
import re

def delete_lines_starting_with_declare_in_string(input_text):
    # Split the input text into lines
    lines = input_text.splitlines()
    
    # Initialize variables
    lines_deleted = 0
    result_lines = []
    
    for line in lines:
        if not line.startswith("(declare"):
            # Append lines that don't start with "(declare" to the result
            result_lines.append(line)
        else:
            lines_deleted += 1

    # Join the lines back together with newline characters
    result_text = "\n".join(result_lines)

    return lines_deleted, result_text

def convert_unformatted_file(filename):
    print('opening file...')
    # Open input file read-only
    input_filename = filename
    input_file = open(filename, 'r')

    # Get contents
    print('getting contents...')
    input_text = input_file.read()

    print('converting to dimacs...')
    output_text = to_dimacs(input_text)

    # Create output file with fixed name
    print('creating output file...')
    output_filename = input_filename.replace('_unformatted', '')
    output_filename = output_filename.replace('.txt', '.cnf')
    output_filename = 'cnf_files/' + output_filename
    output_file = open(output_filename, 'w')
    output_file.write(output_text)


def to_dimacs(text):
    # Create result text
    num_vars, result = delete_lines_starting_with_declare_in_string(text)

    # Remove unnessecary substrings
    removable_substrs = ['(', ')', 'assert', 'or']
    for s in removable_substrs:
        result = result.replace(s, '')

    # Replace 'not' with '-'
    result = result.replace('not', '-')

    # Give variables integers
    result = replace_words_with_integers_preserve_lines(result)
    result = result.replace('- ', '-')
    num_clauses = len(result.splitlines())

    result = f'p cnf {num_vars} {num_clauses}\n' + result

    return result

def replace_words_with_integers_preserve_lines(text):
    # Split the line into words
    words = re.findall(r'\S+|\n', text)
    
    # Create a dictionary to store the mapping of words to unique integers
    word_to_integer = {}
    
    # List to store the result with integers
    result = []
    
    # Iterate through the words and replace each unique word with an integer
    next_integer = 1  # Start with 1 to avoid using 0 (can be adjusted)
    for word in words:
        if word == '-':
            result.append(word)
        elif word == '\n':
            result.append('0\n')
        elif word not in word_to_integer:
            word_to_integer[word] = next_integer
            result.append(str(next_integer))
            next_integer += 1
        else:
            result.append(str(word_to_integer[word]))
    
    # Reassemble the line
    return ' '.join(result)

convert_unformatted_file(sys.argv[1])
