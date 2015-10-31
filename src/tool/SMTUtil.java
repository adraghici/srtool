package tool;

import java.util.Collections;
import java.util.List;

public class SMTUtil {

    /**
     * Generate SMT code for a unary expression wrapping the argument with the given operators.
     */
    public static String unaryExpr(String arg, List<String> ops) {
        Collections.reverse(ops);

        String result = unaryOp(ops.get(0), arg);
        for (int i = 1; i < ops.size(); ++i) {
            result = unaryOp(ops.get(i), result);
        }

        return result;
    }

    /**
     * Generate SMT code for a binary expression with the given arguments and operators.
     * Size of args must always be 1 larger than the size of ops.
     */
    public static String binaryExpr(List<String> args, List<String> ops, Type argsType, Type opType) {
        if (ops.size() == 1) {
            return binaryOp(ops.get(0), args.get(0), args.get(1), argsType, opType);
        }

        return binaryOp(ops.get(ops.size() - 1),
            binaryExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1), argsType, opType),
            args.get(args.size() - 1), argsType, opType);
    }

    /**
     * Generate SMT code for a ternary expression with the given arguments.
     */
    public static String ternaryExpr(List<String> args) {
        if (args.size() == 3) {
            return ternaryOp(toBool(args.get(0)), args.get(1), args.get(2));
        }

        return ternaryOp(toBool(args.get(0)), args.get(1), ternaryExpr(args.subList(2, args.size())));
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
        return toBV32("(" + operator + " " + lhs + " " + rhs + ")");
    }

    private static String binaryOp(String operator, String lhs, String rhs, Type argsType, Type opType) {
        if (argsType == Type.BOOL && opType == Type.BOOL) {
            return toBV32("(" + operator + " " + toBool(lhs) + " " + toBool(rhs) + ")");
        } else if (argsType == Type.INT && opType == Type.BOOL) {
            return toBV32("(" + operator + " " + lhs + " " + rhs + ")");
        } else {
            return "(" + operator + " " + lhs + " " + rhs + ")";
        }
    }

    public static String ternaryOp(String cond, String lhs, String rhs) {
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
                return "(assert false)";
            case 1:
                return assertion("not", asserts.get(0));
            default:
                return assertion("not", andExpressions(asserts));
        }
    }

    public static String andExpressions(List<String> expressions) {
        switch (expressions.size()) {
            case 0:
                return "";
            case 1:
                return expressions.get(0);
            default:
                return SMTUtil.binaryExpr(
                    expressions,
                    Collections.nCopies(expressions.size() - 1, "and"),
                    Type.BOOL,
                    Type.BOOL);
        }
    }

    public enum Type { BOOL, INT }
}
