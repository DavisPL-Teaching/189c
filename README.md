# ECS 189C: Software Correctness - Spring Quarter 2024

## Lectures

To follow along with lectures:

Clone the repo:
```shell
git clone git@github.com:DavisPL-Teaching/189C.git
```

If you have local changes, but haven't committed them, you can stash and then pull
```shell
git stash
git pull
```

Altneratively, if you want to save your work, you can back up your local changes and pull the latest version:
```shell
git fetch --all
git branch backup-changes
git reset --hard origin/main
```

## Course Information

- **Instructor:** Caleb Stanford
- **TA:** Parnian Kamran
- **CRN:** 57484
- **Units:** 4 (please change this in schedule builder!)
- **Listed Title:** Special Topics in Computer Science - Programming Languages and Compilers
- **Schedule:** Monday, Wednesday, Friday 1:10-2pm
- **Location:** Teaching and Learning Complex 1218
- **Final exam:** June 12, 6-8pm (Please note that this is not in schedulebuilder! But it is the correct time for our class slot. 189 final exam dates are not listed because the final exam room is yet to be determined. If they are unable to get us a room, then we will do the final exam in class.)

## Course Description

What does it mean for software to be correct?

In this upper-level undergraduate course, we will explore the principles and practices behind building software that functions as its intended. Through a survey of topics, including model-based verifiers, program verification tools, and advanced type systems, students will gain hands-on experience with writing program models and program specifications using tools used in industry at companies like Amazon and Microsoft.

## Intended Audience and Prerequisites

This course is ideal for mid to upper-level undergraduate computer science majors.
While there are no official prerequisites, the following are unofficial requirements:

- A basic programming background (for example, the ability to write a program like [FizzBuzz](https://www.hackerrank.com/challenges/fizzbuzz/problem)) will be expected. (ECS 36A/36B/36C)
- Some familiarity with discrete mathematics or mathematical proofs (e.g. ECS 20) will be helpful, but not required.
- Some background in formal logic (like PHIL 12 or PHIL 112) is helpful, but not required.

## Learning Objectives

By the end of the course, students will be able to:

1. Understand the concept of software correctness and its importance.
2. Use random testing tools like Hypothesis for software testing.
3. Use model-based verifiers like Z3 for software analysis.
4. Apply program verification tools such as Dafny to ensure the correctness of software.
5. Explore advanced topics in software correctness, including advanced type systems and concurrency.

## Course Schedule

See `schedule.md`.

## Evaluation Criteria

- **Homeworks (55%):** 5 assignments (due bi-weekly), plus homework 0
- **Participation (10%):** via in-class quizzes
- **Final Exam (35%):** covering all topics covered in the course.

## Grade Breakdown

The following are minimum cutoffs: if your grade is above the given percentage, you will definitely receive at least the given grade. However, I reserve the right to lower the cutoffs (i.e. you might get a better grade than what the table says).
This will be used to correct for if assignments or the final were harder than expected.

| Percentage | Minimum Grade |
| --- | --- |
| 93 | A  |
| 90 | A- |
| 87 | B+ |
| 83 | B  |
| 80 | B- |
| 77 | C+ |
| 73 | C  |
| 70 | C- |
| 67 | D+ |
| 63 | D  |
| 60 | D- |

## Grading

For homeworks, your assignments will be graded on the following two broad criteria: correctness and code quality.
The majority of the grade will be based on correctness.
Starting with HW2, you can expect a rough rubric of 90% of the points for correctness and 10% for code quality.

- **Correctness:** Does you program work? That is, does it have the right output on each input and run within a reasonable amount of time? Are your answers to individual questions correct? Does it do everything that's it's supposed to, are there bugs?

- **Code quality:** Does you program exhibit high code quality standards? That is, modular code, readable, not overly complex, well documents, commented, logically separated modules and functions, and reasonably efficient? Are your free response answers thoughtful?

The final exam will be curved.
That means, for example, if 100 points are possible, it may be entered as out of a smaller number of points like 90 or 80 for the purposes of calculating your grade, if the average score of the class was low or if there were unexpectedly difficult questions.
However, I will not announce the curving strategy ahead of time.

## Homeworks and GitHub Classroom

Programming cannot be learned by merely watching or reading, it must be done!
Homeworks will consist of programming assignments designed to bring together concepts we learned in class.
Homeworks will be posted using the class GitHub Classroom page along with the lectures, and announced on Piazza when they are finalized.
There will be instructions for joining the GitHub Classroom when homework 1 is released.

## Attendance and Participation

To encourage class attendance, there are in class polls that are worth a small amount of credit.
However, if you miss class, you may make up the in-class quizzes
by watching the lectures or looking at slides and filling out your quiz responses offline.

## Lecture Recordings and Zoom

**Disclaimer:** I will be broadcasting and recording lectures on Zoom, but this is a best-effort process; I can make no promises that this will work every time, or that it will be as audible/understandable as the in-person lectures.
In particular, please note the following:

- I will share screen, but I won't generally check the Zoom chat for interactions/questions

- I will generally try to face the audience, so it may not be as easy to see what I am talking about through Zoom, or to see things like audience interaction, if we write something on the board, etc.

Despite these caveats, my voice will be audible and you should generally be able to follow along through the slides if you need to.
Zoom recordings will be made available on Canvas.

## AI Policy

AI collaboration is allowed and encouraged for homework assignments. However, the final exam will be in-class and closed-book.
Please see also [Prof. Jason Lowe-Power's advice here](https://jlpteaching.github.io/comparch/syllabus/#using-generative-ai-tools).

## Collaboration Policy and Academic Integrity

This class will encourage collaboration; however, each person should complete their own version of the assignment. **You should not directly copy code from someone else, even within your study group,** but you can receive help and give help on individual parts of an assignment.

You may complete homework assignments in groups of up to 3 people, as long as everyone is working on their own copy of the code. If you do this, please list the names of your collaborators at the top of your submission.

Here are some examples of good (allowed) collaboration:

- Sharing of resources
- Sharing of inspiration
- Sharing questions about the assignment on Piazza
- Helping out classmates on Piazza
- Collaboration at a low level (E.g., hey, what's the syntax for X, again? Why does this code print Y?)
- Collaboration at a high level (Why did they tell us to do this in that way?)
- As in most CS courses, the internet is your friend!

And here are examples of disallowed collaboration:

- Sharing large amounts of code with others within your group or others in the course.
- Sharing the exact solution to a specific mid-level programming problem.
- Asking a stranger to finish your work for you or copying and pasting what you find online for submission.

In other words, please use common sense!
This course strictly follows the [UC Davis Code of Academic Integrity](https://ossja.ucdavis.edu/academic-integrity).

## Late Policy

In-class participation points (polls) as well as HW0 can be made up at any point during the quarter, by submitting the Google form link. The forms will remain open and can be found by viewing the lecture recording or lecture notes for that day.

Homeworks will generally be due at 11:59pm on the due date.

For homeworks, I cannot guarantee that late work will be graded.
However, I encourage you to update your assignments even after the deadline -- GitHub classroom will allow us to see both the state of the code at the time of the deadline as well as any recent changes.
At grading time, we may choose to grade the more recent version at our discretion.

Also, near the end of the quarter, you will be given the opportunity to go back and pick one assignment that you missed points on, and make up the points (up to 50% of the points back that you missed).

## Disclaimers

Communication from the instructor will only be sent through official UC Davis email addresses and channels. Please be vigilant of job scams impersonating faculty members. For more information, visit [UC Davis Job Scams Prevention](https://icc.ucdavis.edu/find/scams).

Please be nice to each other.
UC Davis has [policies against harassment and discrimination](https://hr.ucdavis.edu/departments/elr/preventing-discrimination-harassment).
Be inclusive of your classmates in group discussions.
If you need to, you may reach me by email to report an issue with a classmate.

## Contact and Office Hours

Please use the Piazza for questions related to course material.
I encourage you to ask anonymously if you feel more comfortable.
Also, please ask publicly unless there is a good reason not to.
If you have a question that is more sensitive or unrelated to the course, please email me (at `cdstanford` `ucdavis` `edu`).

The instructor and TAs will be available during office hours for additional support on course material and assignments. The schedule of office hours can be found in a pinned post on Piazza.
