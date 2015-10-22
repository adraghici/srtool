package tool;

import java.util.List;

public class SMTUtil {
    public static String declare(String var, int id) {
        return "(declare-fun " + var + id + " () (_ BitVec 32))\n";
    }

    public static String assertion(String operator, String expr) {
        return "(assert (" + operator + " " + expr + "))\n";
    }

    public static String assertion(String operator, String lhs, String rhs) {
        return "(assert (" + operator + " " + lhs + " " + rhs + "))\n";
    }

    public static String binaryOperator(String operator, String lhs, String rhs) {
        return "(" + operator + " " + lhs + " " + rhs + ")";
    }

    public static String ternaryOperator(String cond, String lhs, String rhs) {
        return "(ite " + cond + " " + lhs + " " + rhs + ")";
    }

    public static String number(String number) {
        return "(_ bv" + number + " 32)";
    }

    public static String toBool(String bv) {
        return "(tobool " + bv + ")";
    }

    /**
     * Generate SMT code for a binary expression with the given arguments and operators.
     * Size of args must always be 1 larger than the size of ops.
     */
    public static String binaryExpression(List<String> args, List<String> ops) {
        if (ops.size() == 1) {
            return binaryOperator(ops.get(0), args.get(0), args.get(1));
        }

        return binaryOperator(
            ops.get(ops.size() - 1),
            binaryExpression(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            args.get(args.size() - 1));
    }

    /**
     * Generate SMT code for a ternary expression with the given arguments.
     */
    public static String ternaryExpression(List<String> args) {
        if (args.size() == 3) {
            return ternaryOperator(args.get(0), args.get(1), args.get(2));
        }

        return ternaryOperator(
            args.get(0),
            args.get(1),
            ternaryExpression(args.subList(2, args.size())));
    }

    public static String convertOperator(String operator) {
        switch (operator) {
            case "+":
                return "bvadd";
            case "-":
                return "bvsub";
            case "*":
                return "bvmul";
            case "/":
                return "bvdiv";
            case "||":
                return "or";
            case "&&":
                return "and";
            case "|":
                return "bvor";
            case "^":
                return "bxor";
            case "&":
                return "band";
            case "==":
                return "=";
            case "!=":
                return "distinct";
            default:
                throw new IllegalArgumentException();
        }
    }
}
