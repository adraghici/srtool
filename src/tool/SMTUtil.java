package tool;

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
}
