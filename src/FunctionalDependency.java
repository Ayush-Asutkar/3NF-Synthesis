import java.util.HashSet;

public class FunctionalDependency {
    private String left;
    private String right;

    public FunctionalDependency(String left, String right) {
        this.left = left;
        this.right = right;
    }

    public String getLeft() {
        return left;
    }

    public String getRight() {
        return right;
    }

    private boolean checkingFD (HashSet<Character> attributes, String str) {
        char[] arr = str.toCharArray();

        for(char i: arr) {
            if(!attributes.contains(i)) {
                return false;
            }
        }

        return true;
    }

    public boolean correctFD (HashSet<Character> attributes) {
        return (checkingFD(attributes, getLeft())  && checkingFD(attributes, getRight()));
    }

    @Override
    public boolean equals(Object obj) {
        FunctionalDependency newObj = (FunctionalDependency) obj;
        boolean leftSide = left.equals(newObj.getLeft());
        boolean rightSide = right.equals(newObj.getRight());

        return leftSide && rightSide;
    }

    @Override
    public String toString() {
        return left + "->" + right;
    }
}
