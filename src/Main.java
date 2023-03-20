import java.util.ArrayList;
import java.util.Scanner;

public class Main {
    private static final AttributesAndFD attributesFD = new AttributesAndFD();

    public static void main(String[] args) {
        System.out.println(Colors.ANSI_RED + "\n\n******For this code, please keep the attributes only of single letter characters.******\n" + Colors.ANSI_RESET);

        Scanner sc = new Scanner(System.in);

        System.out.println(Colors.ANSI_RESET + "Enter all the attributes (space separated): ");
        String input = sc.nextLine();
        attributesFD.addAttributes(input);

        System.out.println(Colors.ANSI_PURPLE + attributesFD + "\n");

        System.out.print(Colors.ANSI_RESET + "Enter the number of functional dependency: ");
        int sizeOfFD = sc.nextInt();
        String backslash = sc.nextLine();
        attributesFD.initializeFD(sizeOfFD);


        System.out.println(Colors.ANSI_RESET + "\nEnter the functional dependency in following format");
        System.out.println("Format:- AB->D");

        for(int i=0; i<attributesFD.getSizeOfFD(); i++) {
            input = sc.nextLine();
            boolean addedCorrectly = attributesFD.addFD(input);
            if(!addedCorrectly) {
                System.out.println(Colors.ANSI_RED + "Entered functional dependency:- " + input + " is not correct, " +
                        "it is having attributes that were not declared.\n" +
                        "Please re-enter the functional dependency");
                i--;
            }
        }

        System.out.println(Colors.ANSI_PURPLE + "\n" + attributesFD);


        //3NF Synthesis with DP
        System.out.println(Colors.ANSI_YELLOW + "Performing 3NF Synthesis with Dependency Preservation and Lossless Join\n");

        ArrayList<Attributes> synthesis = attributesFD.threeNFSynthesis();

        if(synthesis.size() == 1) {
            //already in 3NF
            System.out.println(Colors.ANSI_BLUE + "Given decomposition is already in 3NF");
            System.out.println(synthesis.get(0).getAttributes());
        } else {
            System.out.println(Colors.ANSI_BLUE + "Following is the decomposition");
            int num = 1;
            for(Attributes att: synthesis) {
                System.out.println("R" + num + " => " + att.getAttributes());
                num++;
            }
        }
    }
}
