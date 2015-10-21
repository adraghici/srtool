package tool;

import java.util.List;

public class SMTUtil {
    public static String declare(String var, int id) {
        return "(declare-fun " + var + id + " () (_ BitVec 32))" + "\n";
    }

    public static String assertion(String operator, String expr) {
        return "(assert (" + operator + " " + expr + "))\n";
    }

    public static String assertion(String operator, String lhs, String rhs) {
        return "(assert (" + operator + " " + lhs + " " + rhs + "))\n";
    }

    public static String operator(String operator, String lhs, String rhs) {
        return "(" + operator + " " + lhs + " " + rhs + ")";
    }

    public static String number(String number) {
        return "(_ bv" + number + " 32)";
    }

    /**
     * Generate SMT code for an expression with given 'args' and 'ops'.
     * Size of 'args' must always be 1 larger than the size of 'ops'.
     */
    public static String expression(List<String> args, List<String> ops) {
        int opsSize = ops.size();
        int argsSize = args.size();

        if (opsSize == 1) {
            return operator(ops.get(0), args.get(0), args.get(1));
        }

        return operator(ops.get(opsSize - 1),
                        expression(args.subList(0, argsSize - 1), ops.subList(0, opsSize - 1)),
                        args.get(argsSize - 1));
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
            case "==":
                return "=";
            case "!=":
                return "distinct";
            default:
                throw new IllegalArgumentException();
        }
    }
}
