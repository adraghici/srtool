package tool;

import com.google.common.collect.ImmutableSet;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class SMTUtil {
    public static final String RESULT_PLACEHOLDER = "\\result";
    private static ImmutableSet<String> LOGICAL_OPERATORS = ImmutableSet.of("&&", "||");
    private static ImmutableSet<String> COMPARISON_OPERATORS = ImmutableSet.of("==", "!=", "<", ">", "<=", ">=");

    /**
     * Generate SMT code for a unary expression wrapping the argument with the given operators.
     */
    public static String unaryExpr(String arg, List<String> ops) {
        if (ops.isEmpty()) {
            return arg;
        }

        Collections.reverse(ops);
        String result = unaryOp(ops.get(0), arg);
        for (int i = 1; i < ops.size(); ++i) {
            result = unaryOp(ops.get(i), result);
        }

        return result;
    }

    public static String unaryOp(String operator) {
        switch (operator) {
            case "+":
                return "bvid";
            case "-":
                return "bvneg";
            case "!":
                return "bvtobinary";
            case "~":
                return "bvnot";
            default:
                throw new IllegalArgumentException();
        }
    }

    public static String binaryOp(String operator) {
        switch (operator) {
            case "||":
                return "or";
            case "&&":
                return "and";
            case "|":
                return "bvor";
            case "^":
                return "bvxor";
            case "&":
                return "bvand";
            case "==":
                return "=";
            case "!=":
                return "distinct";
            case "<":
                return "bvslt";
            case "<=":
                return "bvsle";
            case ">":
                return "bvsgt";
            case ">=":
                return "bvsge";
            case "<<":
                return "bvshl";
            case ">>":
                return "bvashr";
            case "+":
                return "bvadd";
            case "-":
                return "bvsub";
            case "*":
                return "bvmul";
            case "/":
                return "bvdiv";
            case "%":
                return "bvsrem";
            default:
                throw new IllegalArgumentException();
        }
    }

    public static String declare(String var, int id) {
        return "(declare-fun " + var + id + " () (_ BitVec 32))\n";
    }

    public static String assertion(String operator, String expr) {
        return "(assert (" + operator + " " + toBool(expr) + "))\n";
    }

    public static String assertion(String operator, String lhs, String rhs) {
        return "(assert (" + operator + " " + lhs + " " + rhs + "))\n";
    }

    public static String unaryOp(String operator, String arg) {
        return "(" + operator + " " + arg + ")";
    }

    public static String binaryOp(String operator, String lhs, String rhs) {
        String op = binaryOp(operator);
        if (LOGICAL_OPERATORS.contains(operator)) {
            return toBV32("(" + op + " " + toBool(lhs) + " " + toBool(rhs) + ")");
        } else if (COMPARISON_OPERATORS.contains(operator)) {
            return toBV32("(" + op + " " + lhs + " " + rhs + ")");
        } else {
            return "(" + op + " " + lhs + " " + rhs + ")";
        }
    }

    public static String ternaryOp(String cond, String lhs, String rhs) {
        return "(ite " + cond + " " + lhs + " " + rhs + ")";
    }

    public static String implies(String lhs, String rhs) {
        return toBV32("(=> " + lhs + " " + rhs + ")");
    }

    public static String and(String lhs, String rhs) {
        return toBV32("(and " + lhs + " " + rhs + ")");
    }

    public static String and(List<String> expressions) {
        StringBuilder result = new StringBuilder();
        result.append("(and ");
        result.append(String.join("",
            expressions.stream().map(expr -> toBool(expr) + " ").collect(Collectors.toList())));
        // Replace space at the end with a matching closing parantheses for 'and'.
        result.replace(result.length()-1, result.length(), ")");
        return toBV32(result.toString());
    }

    public static String number(String number) {
        return "(_ bv" + number + " 32)";
    }

    public static String toBool(String bv) {
        return "(tobool " + bv + ")";
    }

    public static String toBV32(String bool) {
        return "(tobv32 " + bool + ")";
    }

    public static String generateCondition(List<String> asserts) {
        switch (asserts.size()) {
            case 0:
                return "(assert false)";
            case 1:
                return assertion("not", asserts.get(0));
            default:
                return assertion("not", and(asserts));
        }
    }
}
