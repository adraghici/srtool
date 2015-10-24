package tool;

import java.util.Collections;
import java.util.List;

public class SMTUtil {

    public enum Type { BOOL, INT };

    public static String declare(String var, int id) {
        return "(declare-fun " + var + id + " () (_ BitVec 32))\n";
    }

    public static String assertion(String operator, String expr) {
        return "(assert (" + operator + " " + toBool(expr) + "))\n";
    }

    public static String assertion(String operator, String lhs, String rhs) {
        return "(assert (" + operator + " " + lhs + " " + rhs + "))\n";
    }

    public static String unaryOperator(String operator, String arg) {
        return "(" + operator + " " + arg + ")";
    }

    public static String binaryOperator(String operator, String lhs, String rhs, Type argsType, Type opType) {
        if (argsType == Type.BOOL && opType == Type.BOOL) {
            return toBV32("(" + operator + " " + toBool(lhs) + " " + toBool(rhs) + ")");
        } else if (argsType == Type.INT && opType == Type.BOOL) {
            return toBV32("(" + operator + " " + lhs + " " + rhs + ")");
        } else {
            return "(" + operator + " " + lhs + " " + rhs + ")";
        }
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

    public static String toBV32(String bool) {
        return "(tobv32 " + bool + ")";
    }

    public static String generateCondition(List<String> asserts) {
        switch (asserts.size()) {
            case 0:
                return "";
            case 1:
                return assertion("not", asserts.get(0));
            default:
                return assertion("not", SMTUtil.binaryExpression(
                    asserts, Collections.nCopies(asserts.size() - 1, "and"), Type.BOOL, Type.BOOL));
        }
    }

    public static String unaryExpression(String arg, List<String> ops) {
        Collections.reverse(ops);
        String result = unaryOperator(ops.get(0), arg);

        for (int i = 1; i < ops.size(); ++i) {
            result = unaryOperator(ops.get(i), result);
        }

        return result;
    }

    /**
     * Generate SMT code for a binary expression with the given arguments and operators.
     * Size of args must always be 1 larger than the size of ops.
     */
    public static String binaryExpression(List<String> args, List<String> ops, Type argsType, Type opType) {
        if (ops.size() == 1) {
            return binaryOperator(ops.get(0), args.get(0), args.get(1), argsType, opType);
        }

        return binaryOperator(
            ops.get(ops.size() - 1),
            binaryExpression(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1), argsType, opType),
            args.get(args.size() - 1),
            argsType,
            opType);
    }

    /**
     * Generate SMT code for a ternary expression with the given arguments.
     */
    public static String ternaryExpression(List<String> args) {
        if (args.size() == 3) {
            return ternaryOperator(toBool(args.get(0)), args.get(1), args.get(2));
        }

        return ternaryOperator(
            args.get(0),
            args.get(1),
            ternaryExpression(args.subList(2, args.size())));
    }

    public static String convertUnaryOp(String operator) {
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

    public static String convertBinaryOp(String operator) {
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
            default:
                throw new IllegalArgumentException();
        }
    }
}
