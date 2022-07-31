import json
import sys
import os
from xml.etree import ElementTree


def remove_lines(remove_from, lines):
    for line in lines:
        class_line_to_remove = []
        for class_line in remove_from:
            if line.get('number') == class_line.get('number'):
                class_line_to_remove.append(class_line)
        for class_line in class_line_to_remove:
            remove_from.remove(class_line)


def read_stats(directory):
    """ Parse the .json files from the given directory into a dictionary """
    target_methods = {}
    for (dir_path, _, filenames) in os.walk(directory):
        for filename in filenames:
            full_path = os.path.join(dir_path, filename)
            data = " ".join(
                [line.strip("\n") for line in open(full_path).readlines()])
            new_methods = json.loads(data)
            for method in new_methods:
                target_methods[method["compiledName"]] = method
    return target_methods


def filter_by_method(stats_dir, report_file):

    target_methods = read_stats(stats_dir)
    coverage = ElementTree.parse(report_file)
    root = coverage.getroot()

    for package in root.iter('package'):
        classes_to_remove = []
        for clazz in package.iter('class'):
            methods_to_remove = []
            for method in clazz.iter('method'):
                full_name = clazz.get('name').split("`")[0] + '.' + \
                            method.get('name')
                full_name_alt = clazz.get('name').split("`")[0] + '.' + \
                                method.get('name').lstrip("_")
                if full_name in target_methods:
                    target_methods.pop(full_name)
                elif full_name_alt in target_methods:
                    target_methods.pop(full_name_alt)
                else:
                    methods_to_remove.append(method)
            for method in methods_to_remove:
                remove_lines(clazz.find('lines'), method.find('lines'))
                clazz.find('methods').remove(method)
            if len(clazz.find('methods').findall('method')) == 0:
                classes_to_remove.append(clazz)
        for clazz in classes_to_remove:
            package.find('classes').remove(clazz)

    recalculate_rates(root)

    with open(report_file, 'w') as f:
        coverage.write(f, encoding='unicode')
    if len(target_methods) != 0:
        print("Warning - cannot find the following methods in the "
              "coverage report: " + ",".join(target_methods.keys()))


def get_condition_coverage(lines):
    total_branch_num = 0
    total_hit_branch_num = 0
    for line in lines:
        condition_coverage = line.get('condition-coverage')
        open_paren = condition_coverage.index('(')
        slash = condition_coverage.index('/')
        close_paren = condition_coverage.index(')')
        total_hit_branch_num += int(condition_coverage[open_paren + 1:slash])
        total_branch_num += int(condition_coverage[slash + 1:close_paren])
    return total_hit_branch_num, total_branch_num


def recalculate_rates(root):
    overall_line_num = 0
    overall_hit_line_num = 0
    overall_branch_num = 0
    overall_hit_branch_num = 0
    for package in root.iter('package'):
        package_line_num = 0
        package_hit_line_num = 0
        package_branch_num = 0
        package_hit_branch_num = 0
        for clazz in package.iter('class'):
            lines = clazz.find('lines').findall('line')
            line_num = len(lines)
            hit_line_num = sum([x.get("hits") != "0" for x in lines])

            lines_with_conditions = [x for x in lines
                                     if x.get("condition-coverage") is not None]

            (hit_branch_num, branch_num) = get_condition_coverage(
                lines_with_conditions)

            package_line_num += line_num
            package_hit_line_num += hit_line_num
            package_branch_num += branch_num
            package_hit_branch_num += hit_branch_num

            line_rate = str(round(hit_line_num / line_num, 4)) \
                if line_num != 0 else "1"
            branch_rate = str(round(hit_branch_num / branch_num, 4)) \
                if branch_num != 0 else "1"

            clazz.set('line-rate', line_rate)
            clazz.set('branch-rate', branch_rate)

        overall_line_num += package_line_num
        overall_hit_line_num += package_hit_line_num
        overall_branch_num += package_branch_num
        overall_hit_branch_num += package_hit_branch_num

        line_rate = str(round(package_hit_line_num / package_line_num, 4)) \
                if package_line_num != 0 else "1"
        branch_rate = str(round(package_hit_branch_num / package_branch_num, 4)) \
                if package_branch_num != 0 else "1"
        package.set('line-rate', line_rate)
        package.set('branch-rate', branch_rate)
    root.set('line-rate',
             str(round(overall_hit_line_num / overall_line_num, 4)))
    root.set('branch-rate',
             str(round(overall_hit_branch_num / overall_branch_num, 4)))

    root.set('lines-covered', str(overall_hit_line_num))
    root.set('lines-valid', str(overall_line_num))
    root.set('branches-covered', str(overall_hit_branch_num))
    root.set('branches-valid', str(overall_branch_num))


if __name__ == "__main__":
    filter_by_method(sys.argv[1], sys.argv[2])
