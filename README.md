# ECS 189C: Software Correctness - Winter Quarter 2026

## Contents

1. [Welcome and Course Information](#welcome-and-course-information)
2. [Lectures](#lectures)
3. [Course Description](#course-description)
4. [Schedule](#schedule)
5. [Grade Breakdown](#grade-breakdown)
6. [Policies](#policies)
7. [Contact and Office Hours](#contact-and-office-hours)

## Welcome and Course Information

Welcome to ECS 189C!

- **Listed Title:** Special Topics in Computer Science - Programming Languages and Compilers
- **CRN:** 41580
- **Units:** 4 (please change this in schedule builder!)
- **Flyer:** see [here](https://ucdavis.box.com/s/n4zd9b8wkc2thzcmjld5zqc7wfkn5pj1)
- **Instructor:** Caleb Stanford
- **TA:** Jason Yoo
- **Lectures:** Tuesdays and Thursdays, 10:30-11:50am in [Shields Library](https://campusmap.ucdavis.edu/?b=114) room 167
- **Final exam:** Friday, March 20, 10:30am-12:30pm. Please note that this is not in schedulebuilder! But it is the correct time for our class slot. If there are any unexpected changes to the schedule, then we will do the final exam in class.

## Lectures

I often lecture via live coding. I will post the code and lecture materials in this repository.
To follow along with the lectures, clone the repository:
```shell
git clone git@github.com:DavisPL-Teaching/189.git
```

If you make changes to the code after each lecture, you will need to discard them before pulling again.
For example, you can run:
```shell
git stash
git pull
```

### Lecture Recordings and Zoom

All lectures are broadcast and recorded on Zoom, and the recordings are made available on Canvas.
Please note that this is a best-effort process, technical difficulties do occur occasionally
(such as lost video recordings or poor audio quality).
If you miss class, you can make up the lectures and class polls by viewing the recording
at any time prior to the last day of class.

## Course Description

In today's world, software is increasingly more complicated, and seems to malfunction in increasingly surprising ways.
Is it possible to develop software such that it is mathematically impossible for things to go wrong?
What tools might we use to save effort when developing mathematical proofs about software?
And what does it mean for software to be correct or incorrect?

This upper-level undergraduate course is an introduction to formal specification and verification of software from a tool-based perspective. We will survey topics including: writing specifications; difference between testing and verification; program verification tools; automated verification tools and SMT solvers such as Z3; and advanced type systems. Students will gain hands-on experience with writing program models and program specifications using tools used in industry at companies like Amazon and Microsoft.
This course can be considered as an undergraduate version of [ECS 261](github.com/DavisPL-Teaching/261).

### Prerequisites

This course is appropriate for mid- to upper-level undergraduate computer science majors.
While there are no official prerequisites, the following are unofficial requirements:

- A prior class in discrete mathematics or mathematical proofs (e.g. ECS 20) is helpful, and will generally be assumed.
- A basic programming background (for example, the ability to write a program like [FizzBuzz](https://www.hackerrank.com/challenges/fizzbuzz/problem)) will be expected. (ECS 36A/36B/36C)
- A course in formal logic (like PHIL 12 or PHIL 112) is helpful, but not required.

### Learning Objectives

By the end of the course, students will be able to:

1. Understand the concept of software correctness and its importance.
2. Use random testing tools like Hypothesis for software testing.
3. Use model-based verifiers like Z3 for software analysis.
4. Apply program verification tools such as Dafny to ensure the correctness of software.
5. Explore advanced topics in software correctness, such as advanced type systems, safety and liveness properties, and program logics.

## Schedule

See `schedule.md`.

## Grade Breakdown

Your grade is evaluated based on:

- **Participation (10%):** via in-class polls
- **Homeworks (20%):** about 5 assignments planned, plus homework 0
- **Midterm (30%)**: covering the first half of the course
- **Final Exam (40%):** covering all topics covered in the course.

### Attendance and Participation

To encourage class attendance, there are in-class polls that are worth a small amount of credit.
However, if you miss class, you may make up the polls
by watching the lectures and filling out your responses offline.
Polls may be made up at any time prior to the last day of class.

### Homeworks

Homeworks will consist of programming assignments designed to bring together concepts we learned in class
and to give you practice using all of the tools we cover.
I plan to assign about 5 homeworks (due roughly bi-weekly), plus homework 0, which is designed to help you install the relevant software for the course.

**Important: your code must run to get credit!**
Frequently running and testing your code during development is an essential part of computer programming -- and a very important skill in the real world! This includes making sure that your code works on someone else's machine. The graders won't be able to debug your submission, and code that does not run may receive a 0 or at most 50% of partial credit.

For programming assignments, you should put thought into producing a solution that is not only correct but well written, high-quality code.
That is: is it readable, shareable, well-documented, well-commented, logically separated into modules and functions, and reasonably efficient?
Are your free response answers thoughtful?
We will use Gradescope for homework submissions and grading.

### Exams

One midterm and one final exam are planned.
Exams are closed-book, but you may bring a single-sided cheat sheet.
Exams will be graded on Gradescope.

I reserve the right to curve exams (this can only help you). That means, for example, if 100 points are possible, it may be entered as out of a smaller number of points like 95 or 85 for the purposes of calculating your grade, if the average score of the class was low or if there were unexpectedly difficult questions.

### Final Grade

For the final (letter) grade, the following are minimum cutoffs. That is, if your grade is above the given percentage, you will definitely receive at least the given grade. However, I reserve the right to lower the cutoffs (i.e. you might get a better grade than what the table says).
I will use this to help students who may be on the boundary between two grades at the end of the quarter.

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

## Policies

### AI Policy

AI collaboration is allowed for homework assignments.
I encourage you to use AI in a way that is helpful to you, and to use caution that your use of AI is aiding (and not preventing) your own understanding of the material and critical thinking skills.
Exams are held in-class and closed-book.
Please see also [Prof. Jason Lowe-Power's advice here](https://jlpteaching.github.io/comparch/syllabus/#using-generative-ai-tools).

### Collaboration Policy and Academic Integrity

This class will encourage collaboration; however, each person should complete their own version of the assignment. **You should not directly copy code from someone else, even within your study group,** but you can receive help and give help on individual parts of an assignment.
In a real software development job, it is common to seek and get help; this class will be no different!

You may work on homework assignments in groups of up to 3 people, as long as everyone is working on their own copy of the code. If you do this, please list the names of your collaborators at the top of your submission.

Beyond the above: please use common sense!
This course strictly follows the [UC Davis Code of Academic Integrity](https://ossja.ucdavis.edu/academic-integrity).

### Late Policy

In-class participation points (polls) can be made up at any point during the quarter (prior to the last day of class), by submitting the Google form link. The forms will remain open and can be found by viewing the lecture recording or lecture notes for that day.
I will not be able to provide a consolidated list of the form links, as their purpose is to encourage you to attend and
watch the lectures.

Homeworks will generally be due at 11:59pm on the due date.
**I cannot guarantee that late homeworks will be graded;**
however, I encourage you to update your assignments even after the deadline -- Gradescope will allow you to upload late work up to a few days after the assignment deadline.
At grading time, we may choose to grade the more recent version at our discretion.

### Job Scams

Communication from the instructor will only be sent through official UC Davis email addresses and channels. Please be vigilant of job scams impersonating faculty members. For more information, visit [UC Davis Job Scams Prevention](https://careercenter.ucdavis.edu/job-and-internship-search/job-scams).

You can view and report job scam emails at the [Phish Bowl](https://phishbowl.ucdavis.edu/).

### Be Nice!

Finally: **please be kind to each other!**
UC Davis has [policies against harassment and discrimination](https://hr.ucdavis.edu/departments/elr/preventing-discrimination-harassment).
Be inclusive of your classmates in group study, in group work, and in your questions and answers in class.
If you need to, you may reach me by email to report an issue with a classmate.

## Contact and Office Hours

**Please use the Piazza for questions related to course material.**
If you send me an email, I will most likely respond to post your question on Piazza :)

On Piazza, please ask all questions publicly, with only one exception: if your post contains a large snippet of code then make it private. I encourage you to ask anonymously if you feel more comfortable.

The instructor and TAs will be available during office hours for additional support on course material and assignments. The schedule of office hours will be posted in a pinned note on Piazza.

If you have a question that is more sensitive or unrelated to the course, please email me: `cdstanford` `ucdavis` `edu`.
