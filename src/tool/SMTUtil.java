package tool;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class SMTUtil {
    public static final String RESULT_PLACEHOLDER = "\\result";
    private static ImmutableSet<String> LOGICAL_OPERATORS = ImmutableSet.of("&&", "||");
    private static ImmutableSet<String> COMPARISON_OPERATORS =
        ImmutableSet.of("==", "!=", "<", ">", "<=", ">=");

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

    public static String declareBool(String var, int id) {
        return "(declare-fun " + var + id + " () (Bool))\n";
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

    public static String and(List<String> asserts) {
        String result =
            "(and " + String.join(" ", asserts.stream().map(SMTUtil::toBool).collect(Collectors.toList())) + ")";
        return toBV32(result);
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
        if (asserts.size() == 0) {
            return "(assert false)";
        }
        return createProps(asserts) + assertion("not", and(asserts));
    }

    public static String getValues(int size) {
        List<String> props = Lists.newArrayList();
        for (int i = 0; i < size; ++i) {
            props.add("prop" + i);
        }
        return "(get-value (" + String.join(" ", props) + "))\n";
    }

    private static String createProps(List<String> asserts) {
        List<String> propDecls = Lists.newArrayList();
        List<String> propAsserts = Lists.newArrayList();
        for (int i = 0; i < asserts.size(); ++i) {
            propDecls.add(declareBool("prop", i));
            propAsserts.add(assertion("=", "prop" + i, toBool(asserts.get(i))));
        }
        return String.join("", propDecls) + String.join("", propAsserts);
    }

    public static String checkSAT() {
        return "(check-sat)\n";
    }

    public static String predefinedFunctions() {
        return String.join("\n", ImmutableList.of("(set-logic QF_BV)", "(set-option :produce-models true)",
            "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))",
            "(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))",
            "(define-fun bvdiv ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32) (ite (not (= y (_ bv0 32))) (bvsdiv x y) x))",
            "(define-fun bvid ((x (_ BitVec 32))) (_ BitVec 32) x)",
            "(define-fun bvtobinary ((x (_ BitVec 32))) (_ BitVec 32) (ite (not (= x (_ bv0 32))) (_ bv0 32) (_ bv1 32)))"));
    }
}
