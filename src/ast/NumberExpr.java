package ast;

public class NumberExpr implements AtomExpr {
    private final String number;

    public NumberExpr(String number) {
        this.number = number;
    }

    public String getNumber() {
        return number;
    }
}
