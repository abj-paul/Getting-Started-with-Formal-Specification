### **SOLID Principles (Based on Roger S. Pressman’s "Software Engineering: A Practitioner’s Approach")**  

The **SOLID** principles are a set of five design principles that help in building maintainable and scalable object-oriented software. These principles were introduced by **Robert C. Martin (Uncle Bob)** and are widely discussed in software engineering, including **Pressman’s "Software Engineering: A Practitioner’s Approach"**, where they are emphasized as best practices for designing high-quality software.  

---

## **1. Single Responsibility Principle (SRP)**
**Definition:** A class should have only **one reason to change**, meaning it should only have **one responsibility**.  

**Why it’s important?**  
- Improves **modularity** and makes the code **easier to maintain**.  
- Avoids tightly coupled classes where changes in one feature affect unrelated functionalities.  

**Example (Bad Design – Violates SRP):**
```python
class Report:
    def generate_report(self):
        print("Generating report...")
    
    def save_to_database(self):
        print("Saving report to database...")  # Violates SRP
    
    def print_report(self):
        print("Printing report...")  # Violates SRP
```
**Fixed Version (Following SRP):**
```python
class ReportGenerator:
    def generate_report(self):
        print("Generating report...")

class ReportSaver:
    def save_to_database(self):
        print("Saving report to database...")

class ReportPrinter:
    def print_report(self):
        print("Printing report...")
```
Here, each class has **one responsibility**, making the system more maintainable.  

---

## **2. Open/Closed Principle (OCP)**
**Definition:** Software entities (classes, modules, functions) should be **open for extension but closed for modification**.  

**Why it’s important?**  
- Allows **adding new features without modifying existing code**, reducing risk of breaking the system.  

**Example (Bad Design – Violates OCP):**
```python
class Discount:
    def apply_discount(self, price, discount_type):
        if discount_type == "student":
            return price * 0.9
        elif discount_type == "senior":
            return price * 0.8
```
If a new discount type is introduced, this class **must be modified**, violating OCP.  

**Fixed Version (Following OCP – Using Inheritance):**
```python
class Discount:
    def apply_discount(self, price):
        return price  # Default behavior

class StudentDiscount(Discount):
    def apply_discount(self, price):
        return price * 0.9

class SeniorDiscount(Discount):
    def apply_discount(self, price):
        return price * 0.8
```
Now, we can add new discount types without modifying existing code.  

---

## **3. Liskov Substitution Principle (LSP)**
**Definition:** **Subtypes must be substitutable for their base types without altering correctness**.  

**Why it’s important?**  
- Prevents code from **unexpected behavior when using derived classes**.  

**Example (Bad Design – Violates LSP):**
```python
class Bird:
    def fly(self):
        print("Flying...")

class Penguin(Bird):
    def fly(self):
        raise Exception("Penguins cannot fly!")
```
Here, **Penguin** is a subclass of **Bird**, but it breaks the expected behavior of the base class, violating LSP.  

**Fixed Version (Following LSP – Using Composition instead of Inheritance):**
```python
class Bird:
    pass

class FlyingBird(Bird):
    def fly(self):
        print("Flying...")

class Penguin(Bird):
    def swim(self):
        print("Swimming...")
```
Now, **Penguin** is correctly modeled as a non-flying bird.  

---

## **4. Interface Segregation Principle (ISP)**
**Definition:** **Clients should not be forced to depend on interfaces they do not use**.  

**Why it’s important?**  
- Avoids **bloated interfaces** with unnecessary methods.  

**Example (Bad Design – Violates ISP):**
```python
class Worker:
    def work(self):
        pass

    def eat(self):
        pass
```
A **robot** worker does not eat, but it's forced to implement the `eat()` method.  

**Fixed Version (Following ISP – Using Separate Interfaces):**
```python
class Workable:
    def work(self):
        pass

class Eatable:
    def eat(self):
        pass

class Human(Workable, Eatable):
    def work(self):
        print("Working...")
    
    def eat(self):
        print("Eating...")

class Robot(Workable):
    def work(self):
        print("Working...")
```
Now, **Robot** is not forced to implement `eat()`.  

---

## **5. Dependency Inversion Principle (DIP)**
**Definition:** **High-level modules should not depend on low-level modules. Both should depend on abstractions.**  

**Why it’s important?**  
- Reduces **tight coupling** and makes the system more flexible.  

**Example (Bad Design – Violates DIP):**
```python
class Keyboard:
    pass

class Computer:
    def __init__(self):
        self.keyboard = Keyboard()  # Direct dependency
```
Here, **Computer** is tightly coupled to a specific **Keyboard** implementation.  

**Fixed Version (Following DIP – Using Abstraction):**
```python
class KeyboardInterface:
    def type(self):
        pass

class MechanicalKeyboard(KeyboardInterface):
    def type(self):
        print("Typing on a mechanical keyboard...")

class MembraneKeyboard(KeyboardInterface):
    def type(self):
        print("Typing on a membrane keyboard...")

class Computer:
    def __init__(self, keyboard: KeyboardInterface):
        self.keyboard = keyboard  # Inject dependency

computer = Computer(MechanicalKeyboard())  # Now we can easily switch keyboards!
```
Now, **Computer** is **not tightly coupled** to a specific keyboard type.  

---

## **Conclusion**
The **SOLID principles** help in designing **scalable, maintainable, and robust** object-oriented systems. Pressman highlights these principles as **best practices** for software design, ensuring **flexibility, reusability, and reduced coupling**.  

---

Let me know if you need further explanations or examples! 🚀
